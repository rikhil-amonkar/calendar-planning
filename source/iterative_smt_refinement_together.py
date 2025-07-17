import re
import json
import logging
import os
import time
import shutil
import asyncio
import sys
from openai import OpenAI
import httpx
sys.path.append(os.path.dirname(os.path.abspath(__file__)))
from iterative_smt_refinement_enhanced import (
    parse_args,
    execute_python_code,
    format_constraint_feedback,
    evaluate_calendar,
    evaluate_trip,
    evaluate_meeting,
    RateLimiter,
    task_name_map,
    extract_answer_basic,
    normalize_trip_itinerary
)

eval_functions = {
    "calendar": evaluate_calendar,
    "trip": evaluate_trip,
    "meeting": evaluate_meeting
}

TOGETHER_API_KEY = "45dc2c46ec1b95e0a28d5ea72e9db50f18bfd9adea69660d5d0b2be124f8729c"
TOGETHER_MODEL = "Qwen/Qwen2.5-Coder-32B-Instruct"
TOGETHER_API_URL = "https://api.together.xyz/v1/chat/completions"

# Helper for Together.ai chat completions (for code generation only)
async def together_chat_completion(messages, max_tokens=20000, temperature=0.0, stop=None):
    headers = {
        "Authorization": f"Bearer {TOGETHER_API_KEY}",
        "Content-Type": "application/json"
    }
    payload = {
        "model": TOGETHER_MODEL,
        "messages": messages,
        "max_tokens": max_tokens,
        "temperature": temperature,
    }
    if stop:
        payload["stop"] = stop
    async with httpx.AsyncClient(timeout=60) as client:
        response = await client.post(TOGETHER_API_URL, headers=headers, json=payload)
        response.raise_for_status()
        return response.json()["choices"][0]["message"]["content"]

# --- BEGIN: Copy from iterative_smt_refinement_enhanced.py ---
def get_openai_client():
    """Get OpenAI client for GPT-based extraction"""
    try:
        with open("../../scheduling_key.json") as f:
            key = json.load(f)["openai"]
        return OpenAI(api_key=key)
    except (FileNotFoundError, KeyError):
        logging.warning("Could not initialize OpenAI client for extraction")
        return None

def smart_extract_code(response_txt):
    """
    Smart code extraction using GPT when traditional regex fails
    """
    # First try traditional regex extraction
    matches = re.findall(r"```python\s*(.*?)```", response_txt, re.DOTALL)
    if matches:
        return matches[-1].strip()
    
    # If no code blocks found, try to extract code using GPT
    client = get_openai_client()
    if not client:
        logging.warning("OpenAI client not available, falling back to basic extraction")
        return ""
    
    try:
        prompt = f"""Extract the Python code from the following text. Look for any Python code that might solve a scheduling problem using Z3 solver.\n\nText:\n{response_txt}\n\nIf you find Python code, return ONLY the code without any markdown formatting or explanations.\nIf no Python code is found, return an empty string.\n\nFocus on:\n1. Code that imports and uses Z3 solver\n2. Code that defines variables, constraints, and solves problems\n3. Code that prints or returns results\n\nReturn only the Python code:"""

        response = client.chat.completions.create(
            model="gpt-4o-mini",
            messages=[{"role": "user", "content": prompt}],
            temperature=0,
            max_tokens=2000
        )
        
        extracted_code = response.choices[0].message.content.strip()
        
        # Clean up the extracted code
        if extracted_code.startswith("```python"):
            extracted_code = extracted_code[9:]
        if extracted_code.endswith("```"):
            extracted_code = extracted_code[:-3]
        
        return extracted_code.strip()
        
    except Exception as e:
        logging.error(f"Error in smart code extraction: {e}")
        return ""

def smart_extract_execution_result(execution_output, task):
    """
    Smart extraction of execution results using GPT
    Handles various output formats including errors and no-plan scenarios
    """
    client = get_openai_client()
    if not client:
        logging.warning("OpenAI client not available, falling back to basic extraction")
        return extract_answer_basic(execution_output, task)
    
    try:
        # Determine the expected output format based on task
        if task == "calendar":
            expected_format = '{"day": "Monday", "start_time": "14:30", "end_time": "15:30"}'
        elif task == "trip":
            expected_format = '{"itinerary": [{"day_range": "Day 1-3", "place": "Venice"}, {"day_range": "Day 3-5", "place": "Vienna"}]}'
        elif task == "meeting":
            expected_format = '{"itinerary": [{"action": "meet", "person": "David", "start_time": "13:00", "end_time": "14:00"}]}'
        
        prompt = f"""Extract structured data from the following execution output for a {task} planning task.\n\nExecution Output:\n{execution_output}\n\nExpected format: {expected_format}\n\nInstructions:\n1. If the output contains valid JSON in the expected format, extract and return it\n2. If the output indicates no plan was found or if the output is empty (like \"\", \"No valid itinerary found\", \"No solution found\", \"UNSAT\", \"unsat\", etc.), return {{\"no_plan\": \"reason\"}}\n3. If the output contains an execution error message (like \"Error:\", \"Exception:\", \"Traceback:\", etc.), return {{\"error\": \"error_message\"}}\n4. If the output is malformed or unclear, try to extract any useful information or return {{\"error\": \"malformed_output\"}}\n\nReturn only valid JSON:"""

        response = client.chat.completions.create(
            model="gpt-4o-mini",
            messages=[{"role": "user", "content": prompt}],
            response_format={"type": "json_object"},
            temperature=0,
            max_tokens=1000
        )
        
        result = json.loads(response.choices[0].message.content)
        return result
        
    except Exception as e:
        logging.error(f"Error in smart execution result extraction: {e}")
        return extract_answer_basic(execution_output, task)
# --- END: Copy from iterative_smt_refinement_enhanced.py ---

# Remove OpenAI/Kani engine initialization and use Together for all LLM completions
# For code generation, use together_chat_completion with the prompt and conversation
# For extraction, use smart_extract_code and smart_extract_execution_result as above

# Remove all OpenAIEngine, HuggingEngine, Kani, and get_openai_client code
# Remove any references to keys["openai"] or keys["deepseek"]

# The rest of the script (data loading, execution, evaluation, etc.) remains unchanged except for LLM calls 

async def process_single_example_together(
    example_id,
    example,
    constraints,
    max_passes,
    rate_limiter,
    semaphore,
    task,
    args
):
    """Process a single example using Together.ai for code generation with full conversation history."""
    output_dir = f"../output/SMT/Qwen2.5-Coder-32B-Instruct/{task}/n_pass/{example_id}"
    os.makedirs(output_dir, exist_ok=True)
    logging.info(f"[{example_id}] Output directory: {output_dir}")

    # Prepare initial system and user prompt
    system_prompt = "You are an expert at scheduling meetings using Z3."
    user_prompt = f"Given the following scheduling problem:\n{example['prompt_0shot']}\n"
    if task == "calendar":
        user_prompt += "Your solution should always have three things: the day to meet, the start time, and the end time.\n"
        user_prompt += "Your output should be a string that starts with 'SOLUTION:' followed by three lines in this exact format:\nDay: <day>\nStart Time: <HH:MM> (24-hour format)\nEnd Time: <HH:MM> (24-hour format)\n"
    if task == "trip":
        user_prompt += "Note that if one flies from city A to city B on day X, then they are in both cities A and B on day X, which contributes to the total number of days in each city.\n"
        user_prompt += "Your output should be a JSON-formatted dictionary with an 'itinerary' key containing a list of day-place mappings.\n"
        user_prompt += "Do not include separate flight entries in the JSON output.\n"
        user_prompt += "IMPORTANT: When you fly from city A to city B on day X, that day counts for BOTH cities. For example:\n"
        user_prompt += "- If you stay in Venice from Day 1-3 and fly to Vienna on Day 3, then:\n"
        user_prompt += "  - Venice: Day 1-3 (3 days)\n"
        user_prompt += "  - Vienna: Day 3-6 (4 days, including the flight day)\n"
        user_prompt += "- The flight day (Day 3) is counted for both Venice and Vienna.\n"
        user_prompt += "- Do NOT create separate flight entries in the JSON.\n"
    if task == "meeting":
        user_prompt += "Your output should be a JSON-formatted dictionary with an 'itinerary' key containing a list of meeting entries.\n"
        user_prompt += "Each meeting entry should have the following format:\n"
        user_prompt += '{"action": "meet", "person": "<person_name>", "start_time": "<HH:MM>", "end_time": "<HH:MM>"}\n'
        user_prompt += "The time should be in 24-hour format. For example:\n"
        user_prompt += '{"itinerary": [{"action": "meet", "person": "David", "start_time": "13:00", "end_time": "14:00"}]}\n'
    user_prompt += "Write a Python program that solves it using the Z3 solver. Always surround your final code with ```python\nYOUR_CODE\n```.\n"

    messages = [
        {"role": "system", "content": system_prompt},
        {"role": "user", "content": user_prompt}
    ]
    conversation_history = []

    for pass_num in range(1, max_passes + 1):
        pass_output_dir = f"{output_dir}/{pass_num}_pass"
        os.makedirs(pass_output_dir, exist_ok=True)
        logging.info(f"[{example_id}] Starting pass {pass_num}")

        # Call Together.ai for code generation with full conversation history
        code_gen_start = time.time()
        response_txt = await together_chat_completion(messages, max_tokens=2000, temperature=0.0)
        code_gen_time = time.time() - code_gen_start
        logging.info(f"[{example_id}] Together.ai code generation completed in {code_gen_time:.2f}s")

        # Add to conversation history and messages
        conversation_history.append({"role": "user", "content": messages[-1]["content"]})
        conversation_history.append({"role": "assistant", "content": response_txt})
        messages.append({"role": "assistant", "content": response_txt})

        # Save conversation
        with open(f"{pass_output_dir}/conversation.json", "w") as f:
            json.dump(conversation_history, f, indent=4)

        # Extract and save code using smart extraction
        generated_code = smart_extract_code(response_txt)
        if not generated_code:
            logging.error(f"[{example_id}] No code found in model response")
            error_eval_result = {
                "has_execution_error": True,
                "execution_output": "No code found in model response",
                "pred": {},
                "status": "No code extracted",
                "violated_constraint": {},
                "constraints_satisfied": False,
                "pass_number": pass_num
            }
            with open(f"{pass_output_dir}/evaluation.json", "w") as f:
                json.dump(error_eval_result, f, indent=4)
            feedback = "Code extraction from the previous response failed. Please provide a complete Python solution using the Z3 solver. Make sure to surround your final code with ```python\nYOUR_CODE\n```.\n\nOriginal problem:\n" + example['prompt_0shot']
            messages.append({"role": "user", "content": feedback})
            continue
        code_path = f"{pass_output_dir}/solution.py"
        with open(code_path, "w") as f:
            f.write(generated_code)

        # Execute code
        execution_output = execute_python_code(code_path)
        with open(f"{pass_output_dir}/output.out", "w") as f:
            f.write(execution_output)

        try:
            # Extract structured answer from execution output using smart extraction
            pred_formatted = smart_extract_execution_result(execution_output, task)
            # Evaluate constraints and prepare feedback
            eval_func = eval_functions[task]
            constraints_satisfied, violated_constraints = eval_func(constraints, pred_formatted)

            # Get gold answer
            gold = example.get("golden_plan", "")
            if isinstance(gold, list):
                gold = "\n".join(gold)
            logging.info(f"[{example_id}] Raw gold answer: {gold}")
            try:
                gold_formatted = extract_answer_basic(gold, task)
                logging.info(f"[{example_id}] Extracted gold: {gold_formatted}")
            except Exception as e:
                logging.error(f"[{example_id}] Failed to extract gold: {e}")
                gold_formatted = {}

            # Compute is_exact_match
            execution_error = None
            no_plan_found = False
            if isinstance(pred_formatted, dict):
                if "error" in pred_formatted:
                    execution_error = pred_formatted["error"]
                elif "no_plan" in pred_formatted:
                    no_plan_found = True
            is_exact_match = False
            if not execution_error and not no_plan_found:
                if task == "trip":
                    normalized_pred = normalize_trip_itinerary(pred_formatted)
                    normalized_gold = normalize_trip_itinerary(gold_formatted)
                    is_exact_match = normalized_pred == normalized_gold
                else:
                    is_exact_match = pred_formatted == gold_formatted

            # Save evaluation result
            eval_result = {
                "has_execution_error": False,
                "execution_output": execution_output,
                "pred": pred_formatted,
                "gold": gold_formatted,
                "status": "Correct" if constraints_satisfied else "Wrong plan",
                "violated_constraint": violated_constraints,
                "is_exact_match": is_exact_match,
                "constraints_satisfied": constraints_satisfied,
                "pass_number": pass_num
            }
            with open(f"{pass_output_dir}/evaluation.json", "w") as f:
                json.dump(eval_result, f, indent=4)

            # Feedback prompt logic (match enhanced script)
            if execution_error:
                feedback_message = (
                    f"The previous Z3 solution returned an error: {execution_output}\n\n"
                    "Please revise your Z3 program to fix this error. The error suggests there may be an issue with the Z3 code.\n\n"
                    "Make sure to surround your final code with ```python\nYOUR_CODE\n```."
                )
            elif no_plan_found:
                feedback_message = (
                    "The previous Z3 solution failed to find a plan.\n\n"
                    "Please adjust your Z3 program to find a solution.\n\n"
                    "Make sure to surround your final code with ```python\nYOUR_CODE\n```."
                )
            elif not constraints_satisfied:
                plan_summary = f"Plan found: {pred_formatted}"
                feedback_message = (
                    f"The previous solution produced the following plan:\n{plan_summary}\n\n"
                    "However, this plan is incorrect and violates some constraints. Please revise your Z3 program to find a valid solution that satisfies all constraints.\n\n"
                    "Make sure to surround your final code with ```python\nYOUR_CODE\n```."
                )
            else:
                feedback_message = "All constraints satisfied."
            messages.append({"role": "user", "content": feedback_message})

        except Exception as e:
            logging.error(f"[{example_id}] Exception during evaluation or file writing: {e}")
            error_eval_result = {
                "has_execution_error": True,
                "execution_output": execution_output,
                "pred": {},
                "status": f"Exception: {e}",
                "violated_constraint": {},
                "constraints_satisfied": False,
                "pass_number": pass_num
            }
            with open(f"{pass_output_dir}/evaluation.json", "w") as f:
                json.dump(error_eval_result, f, indent=4)

        # Early stop if solved
        if 'constraints_satisfied' in locals() and constraints_satisfied:
            logging.info(f"[{example_id}] SUCCESS! Solved in pass {pass_num}")
            break

async def main():
    args = parse_args()
    logging.info(f"Starting Together AI iterative SMT refinement")
    logging.info(f"Task: {args.task}")
    logging.info(f"Max passes: {args.max_passes}")
    logging.info(f"Max concurrent: {args.max_concurrent}")
    logging.info(f"Rate limit: {args.rate_limit} requests/minute")

    data_path = f"../data/{task_name_map[args.task]}_100.json"
    constraints_path = f"../data/{task_name_map[args.task]}_100_constraints.json"
    try:
        with open(data_path, 'r') as f:
            data = json.load(f)
        with open(constraints_path, 'r') as f:
            constraints_data = json.load(f)
        logging.info(f"Loaded {len(data)} examples from {data_path}")
        logging.info(f"Loaded constraints from {constraints_path}")
    except FileNotFoundError as e:
        logging.error(f"Data file not found: {e}")
        return

    if args.examples:
        example_numbers = [int(x.strip()) for x in args.examples.split(',')]
        examples_to_process = []
        for num in example_numbers:
            example_id = f"{task_name_map[args.task]}_example_{num}"
            if example_id in data:
                examples_to_process.append((example_id, data[example_id]))
            else:
                logging.warning(f"Example {example_id} not found in data, skipping")
    elif args.start is not None or args.end is not None:
        logging.info(f"Filtering examples: start={args.start}, end={args.end}")
        examples_list = list(data.items())
        start_idx = args.start if args.start is not None else 0
        end_idx = args.end if args.end is not None else len(examples_list)
        filtered_examples_list = examples_list[start_idx:end_idx]
        examples_to_process = filtered_examples_list
        logging.info(f"Filtered to {len(examples_to_process)} examples (indices {start_idx} to {end_idx-1})")
    else:
        examples_to_process = list(data.items())

    logging.info(f"Processing {len(examples_to_process)} examples")

    if args.fresh:
        output_base = f"../output/SMT/Qwen2.5-Coder-32B-Instruct/{args.task}/n_pass"
        if os.path.exists(output_base):
            shutil.rmtree(output_base)
            logging.info(f"Cleared output directory: {output_base}")

    rate_limiter = RateLimiter(args.rate_limit / 60.0)
    semaphore = asyncio.Semaphore(args.max_concurrent)
    start_time = time.time()
    
    # Process examples with proper concurrency control
    async def process_with_semaphore(example_id, example, constraints):
        async with semaphore:
            return await process_single_example_together(
                example_id, example, constraints, args.max_passes, rate_limiter, semaphore, args.task, args
            )
    
    # Create tasks but let semaphore control concurrency
    tasks = []
    for example_id, example in examples_to_process:
        constraints = constraints_data.get(example_id, {}).get("constraints", {})
        task = asyncio.create_task(
            process_with_semaphore(example_id, example, constraints)
        )
        tasks.append(task)
    
    # Wait for all tasks to complete
    await asyncio.gather(*tasks, return_exceptions=True)
    total_time = time.time() - start_time
    logging.info(f"Completed processing {len(examples_to_process)} examples in {total_time:.2f} seconds")
    logging.info(f"Average time per example: {total_time / len(examples_to_process):.2f} seconds")

if __name__ == "__main__":
    asyncio.run(main()) 