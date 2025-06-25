"""
Parallel Iterative SMT Refinement with Constraint Feedback

Optimized version that processes multiple examples concurrently to improve efficiency.
"""

import argparse
import json
import os
import subprocess
import asyncio
import re
import time
from datetime import datetime
from kani import Kani
from kani.engines.huggingface import HuggingEngine
from kani.engines.openai import OpenAIEngine
import concurrent.futures
from typing import List, Dict, Any
import logging
import shutil

# Configure logging for timestamps
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    datefmt='%Y-%m-%d %H:%M:%S'
)

def parse_args():
    """Parse command line arguments"""
    parser = argparse.ArgumentParser(description="Run iterative SMT refinement with parallel processing")
    parser.add_argument("--model", type=str, required=True, help="Model to use (e.g., 'DeepSeek-R1')")
    parser.add_argument("--task", type=str, required=True, choices=["calendar", "trip", "meeting"], help="Task type")
    parser.add_argument("--max_passes", type=int, default=5, help="Maximum number of refinement passes")
    parser.add_argument("--max_concurrent", type=int, default=10, help="Maximum number of concurrent examples to process")
    parser.add_argument("--rate_limit", type=int, default=60, help="Rate limit (requests per minute)")
    parser.add_argument("--start", type=int, help="Start example number (inclusive)")
    parser.add_argument("--end", type=int, help="End example number (exclusive)")
    parser.add_argument("--fresh", action="store_true", help="Clear all output directories before running")
    parser.add_argument("--examples", type=str, help="Comma-separated list of example numbers to run (e.g., '25,35')")
    parser.add_argument("--skip_extract", action="store_true", help="Force skip extract_answer for all tasks (default: True for trip tasks)")
    parser.add_argument("--use_extract", action="store_true", help="Force use extract_answer for all tasks (overrides default)")
    
    args = parser.parse_args()
    
    # Clean up examples argument
    if args.examples:
        # Remove all quotes and whitespace
        args.examples = args.examples.replace('"', '').replace("'", "").strip()
        # Split and clean each number
        args.examples = ','.join(num.strip() for num in args.examples.split(','))
    
    return args

try:
    with open("../../scheduling_key.json") as f:
        keys = json.load(f)
except FileNotFoundError:
    print("Error: scheduling_key.json not found. Please create this file with your API keys.")
    exit(1)

def initialize_model(model_name, keys):
    """Initializes the Kani AI model based on the model name."""
    if model_name.startswith("gpt") or model_name.startswith("o"):
        if model_name == "o3-mini":
            model_name = "o3-mini-2025-01-31"
        elif model_name == "gpt-4o-mini":
            model_name = "gpt-4o-mini-2024-07-18"
        engine = OpenAIEngine(keys["openai"], model=model_name, max_context_size=20000)
    elif model_name == "DeepSeek-R1":
        engine = OpenAIEngine(keys["deepseek"], model="deepseek-reasoner", api_base="https://api.deepseek.com", max_context_size=20000)
    elif model_name == "DeepSeek-V3":
        engine = OpenAIEngine(keys["deepseek"], model="deepseek-chat", api_base="https://api.deepseek.com", max_context_size=20000)
    else:
        engine = HuggingEngine(model_id=model_name)

    ai = Kani(engine, system_prompt="")
    return ai

def extract_code(response_txt):
    matches = re.findall(r"```python\s*(.*?)```", response_txt, re.DOTALL)
    return matches[-1].strip() if matches else ""

def extract_answer(answer_str, task):
    """Extract structured answer from text output using GPT-4.1-nano"""
    from openai import OpenAI
    
    try:
        with open("../../scheduling_key.json") as f:
            key = json.load(f)["openai"]
        client = OpenAI(api_key=key)
    except (FileNotFoundError, KeyError):
        print("Warning: Could not initialize OpenAI client for answer extraction")
        return {}
    
    # If answer_str is None or empty, return empty dict
    if not answer_str:
        return {}
        
    # For meeting task, try to extract meeting information even if it doesn't start with SOLUTION:
    if task == "meeting":
        # Look for patterns like "Meet X at Y from HH:MM to HH:MM" or "Meet X (Y) from HH:MM to HH:MM"
        meetings = []
        lines = answer_str.split('\n')
        for line in lines:
            # Try different patterns
            patterns = [
                r"Meet\s+(\w+)\s+(?:at\s+)?(?:[^(]+)?(?:\([^)]+\))?\s+from\s+(\d{1,2}:\d{2})\s+(?:AM|PM)?\s+to\s+(\d{1,2}:\d{2})\s+(?:AM|PM)?",
                r"Meet\s+(\w+)\s+(?:at\s+)?(?:[^(]+)?(?:\([^)]+\))?\s+(\d{1,2}:\d{2})\s+(?:AM|PM)?\s+to\s+(\d{1,2}:\d{2})\s+(?:AM|PM)?",
                r"(\w+):\s+from\s+(\d{1,2}:\d{2})\s+(?:AM|PM)?\s+to\s+(\d{1,2}:\d{2})\s+(?:AM|PM)?"
            ]
            
            for pattern in patterns:
                match = re.search(pattern, line, re.IGNORECASE)
                if match:
                    person = match.group(1)
                    start_time = match.group(2)
                    end_time = match.group(3)
                    
                    # Convert to 24-hour format if needed
                    if "PM" in line and int(start_time.split(':')[0]) < 12:
                        start_hour = int(start_time.split(':')[0]) + 12
                        start_time = f"{start_hour:02d}:{start_time.split(':')[1]}"
                    if "PM" in line and int(end_time.split(':')[0]) < 12:
                        end_hour = int(end_time.split(':')[0]) + 12
                        end_time = f"{end_hour:02d}:{end_time.split(':')[1]}"
                    if "AM" in line and int(start_time.split(':')[0]) == 12:
                        start_time = f"00:{start_time.split(':')[1]}"
                    if "AM" in line and int(end_time.split(':')[0]) == 12:
                        end_time = f"00:{end_time.split(':')[1]}"
                    
                    meetings.append({
                        "action": "meet",
                        "person": person,
                        "start_time": start_time,
                        "end_time": end_time
                    })
                    break
        
        if meetings:
            return {"itinerary": meetings}
    
    # If we couldn't extract meetings or it's not a meeting task, use GPT
    prompt = {
        "calendar": "Given the following time range:\n" + answer_str + "\nExtract the meeting start day and time in a JSON like {\"day\": \"Monday\", \"start_time\": \"14:30\", \"end_time\": \"15:30\"}. The time should be in 24-hour format. If no time range is given at all, output an empty JSON.",
        "trip": "Given the following itinerary:\n" + answer_str + "\nExtract the days spent in each city in a JSON format like {\"itinerary\": [{\"day_range\": \"Day 1-4\", \"place\": \"Tallinn\"}, {\"day_range\": \"Day 4\", \"place\": \"Tallinn\"}, {\"day_range\": \"Day 4\", \"place\": \"Munich\"}, {\"day_range\": \"Day 4-6\", \"place\": \"Munich\"}]}. Preserve the original day ranges as they appear in the output. For flight days, create separate records for both the departure city and arrival city. For flight days, repeat the day record for both the departure city and arrival city (e.g., if staying in Venice from Day 1-3 and flying to Vienna on Day 3, include {\"day_range\": \"Day 1-3\", \"place\": \"Venice\"}, {\"day_range\": \"Day 3\", \"place\": \"Venice\"}, {\"day_range\": \"Day 3\", \"place\": \"Vienna\"}, {\"day_range\": \"Day 3-5\", \"place\": \"Vienna\"}). The day range should be inclusive. If no itinerary is given, output an empty JSON.",
        "meeting": "Given the following meeting schedule:\n" + answer_str + "\nExtract the time and the person of each meeting in a JSON format like {\"itinerary\": [{\"action\": \"meet\", \"person\": \"David\",\"start_time\": \"13:00\", \"end_time\": \"14:00\"}, ...]}. Do not include location. Only keep the meeting times, and ignore time for starting, waiting, or traveling. The time should be converted to a 24-hour format. If no time range is given at all, output an empty JSON"
    }
    
    try:
        response = client.responses.create(
            model="gpt-4.1-nano",
            input=[
                {
                "role": "user",
                "content": [
                    {
                        "type": "input_text",
                        "text": prompt[task]
                    }
                ]
                }
            ],
            text={
                "format": {
                "type": "json_object"
                }
            },
            reasoning={},
            tools=[],
            temperature=0,
            max_output_tokens=2000,
            top_p=1,
            store=True
        )
        output_json = response.output[0].content[0].text
        return json.loads(output_json)
    except Exception as e:
        print(f"Error in answer extraction: {e}")
        return {}

def normalize_trip_itinerary(itinerary):
    """Normalize trip itinerary for comparison by sorting segments and removing duplicates"""
    if not itinerary or "itinerary" not in itinerary:
        return itinerary
    
    segments = itinerary["itinerary"]
    
    # Sort segments by start day, then by place
    sorted_segments = sorted(segments, key=lambda x: (
        int(x["day_range"].replace("Day ", "").split("-")[0]), 
        x["place"]
    ))
    
    return {"itinerary": sorted_segments}

# Import evaluation functions from the original script
from iterative_smt_refinement import (
    evaluate_calendar, evaluate_trip, evaluate_meeting, 
    format_constraint_feedback, execute_python_code
)

eval_functions = {
    "calendar": evaluate_calendar,
    "trip": evaluate_trip,
    "meeting": evaluate_meeting
}

task_name_map = {
    "calendar": "calendar_scheduling",
    "trip": "trip_planning",
    "meeting": "meeting_planning"
}

class RateLimiter:
    """Simple rate limiter to avoid API limits"""
    def __init__(self, requests_per_second: float):
        self.requests_per_second = requests_per_second
        self.last_request_time = 0
    
    async def wait(self):
        if self.requests_per_second <= 0:
            return
        
        current_time = time.time()
        time_since_last = current_time - self.last_request_time
        min_interval = 1.0 / self.requests_per_second
        
        if time_since_last < min_interval:
            wait_time = min_interval - time_since_last
            await asyncio.sleep(wait_time)
        
        self.last_request_time = time.time()

async def run_model_with_rate_limit(ai, prompt, rate_limiter):
    """Run the AI model with rate limiting"""
    await rate_limiter.wait()
    response = await ai.chat_round_str(prompt)
    return response

async def process_single_example(
    example_id,
    example,
    constraints,
    model,
    max_passes,
    rate_limiter,
    semaphore,
    task,
    args
):
    """Process a single example with rate limiting and semaphore"""
    # Initialize variables that might be referenced in error handling
    gold_formatted = {}
    pred_formatted = {}
    violated_constraints = {}
    is_exact_match = False
    constraints_satisfied = False
    execution_output = ""
    pass_num = 0
    
    async with semaphore:
        try:
            # Get task prefix for output directory
            task_prefix_map = {
                "calendar": "calendar_scheduling",
                "trip": "trip_planning",
                "meeting": "meeting_planning"
            }
            task_prefix = task_prefix_map[task]
            
            # Verify example_id matches task prefix
            if not example_id.startswith(f"{task_prefix}_example_"):
                logging.warning(f"Example ID {example_id} does not match expected format for task {task}, skipping")
                return
            
            output_dir = f"../output/SMT/{model}/{task}/n_pass/{example_id}"
            os.makedirs(output_dir, exist_ok=True)
            
            logging.info(f"[{example_id}] Starting processing with model {model}")
            logging.info(f"[{example_id}] Output directory: {output_dir}")
            
            # Initialize AI model
            try:
                with open("../../scheduling_key.json") as f:
                    keys = json.load(f)
                ai = initialize_model(model, keys)
                logging.info(f"[{example_id}] Model initialized successfully")
            except Exception as e:
                logging.error(f"[{example_id}] Failed to initialize model: {str(e)}")
                # Save error evaluation result
                error_eval_result = {
                    "has_execution_error": True,
                    "execution_output": f"Model initialization failed: {str(e)}",
                    "pred": {},
                    "gold": {},
                    "status": "Model initialization error",
                    "violated_constraint": {},
                    "is_exact_match": False,
                    "constraints_satisfied": False,
                    "pass_number": 0
                }
                with open(f"{output_dir}/1_pass/evaluation.json", "w") as f:
                    json.dump(error_eval_result, f, indent=4)
                return
            
            # Initialize conversation history
            conversation_history = []
            
            # Initial prompt
            prompt_prep_start = time.time()
            initial_prompt = "Given the following scheduling problem:\n"
            initial_prompt += f"{example['prompt_0shot']}\n"

            if task == "calendar":
                initial_prompt += "Your solution should always have three things: the day to meet, the start time, and the end time.\n"
                initial_prompt += "Your output should be a string that starts with 'SOLUTION:' followed by three lines in this exact format:\nDay: <day>\nStart Time: <HH:MM> (24-hour format)\nEnd Time: <HH:MM> (24-hour format)\n"
            if task == "trip":
                initial_prompt += "Note that if one flies from city A to city B on day X, then they are in both cities A and B on day X, which contributes to the total number of days in each city.\n"
                initial_prompt += "Your output should be a JSON-formatted dictionary with an 'itinerary' key containing a list of day-place mappings.\n"
                initial_prompt += "For flight days, create separate records for both the departure city and arrival city.\n"
                initial_prompt += "For flight days, repeat the day record for both the departure city and arrival city (e.g., if staying in Venice from Day 1-3 and flying to Vienna on Day 3, include {\"day_range\": \"Day 1-3\", \"place\": \"Venice\"}, {\"day_range\": \"Day 3\", \"place\": \"Venice\"}, {\"day_range\": \"Day 3\", \"place\": \"Vienna\"}, {\"day_range\": \"Day 3-5\", \"place\": \"Vienna\"}).\n"
                initial_prompt += "Example structure: {\"itinerary\": [{\"day_range\": \"Day 1-3\", \"place\": \"Venice\"}, {\"day_range\": \"Day 3\", \"place\": \"Venice\"}, {\"day_range\": \"Day 3\", \"place\": \"Vienna\"}, {\"day_range\": \"Day 3-5\", \"place\": \"Vienna\"}]}\n"
            initial_prompt += "Write a Python program that solves it using the Z3 solver. Always surround your final code with ```python\nYOUR_CODE\n```.\n"
            
            current_prompt = initial_prompt
            prompt_prep_time = time.time() - prompt_prep_start
            logging.info(f"[{example_id}] Prompt prepared - {prompt_prep_time:.2f}s")
            
            for pass_num in range(1, max_passes + 1):
                pass_start_time = time.time()
                logging.info(f"[{example_id}] Starting pass {pass_num}")
                
                # Create output directory for this pass
                dir_create_start = time.time()
                pass_output_dir = f"{output_dir}/{pass_num}_pass"
                os.makedirs(pass_output_dir, exist_ok=True)
                dir_create_time = time.time() - dir_create_start
                
                # Get response from model with rate limiting
                api_call_start = time.time()
                retry_count = 0
                max_retries = 3
                while retry_count < max_retries:
                    try:
                        logging.info(f"[{example_id}] Making API call (attempt {retry_count + 1})")
                        response_txt = await run_model_with_rate_limit(ai, current_prompt, rate_limiter)
                        logging.info(f"[{example_id}] API call successful")
                        break
                    except Exception as e:
                        retry_count += 1
                        logging.warning(f"[{example_id}] API error in pass {pass_num} (attempt {retry_count}): {e}")
                        if retry_count >= max_retries:
                            logging.error(f"[{example_id}] Max retries reached, giving up")
                            # Save error evaluation result
                            error_eval_result = {
                                "has_execution_error": True,
                                "execution_output": f"Max API retries ({max_retries}) reached in pass {pass_num}",
                                "pred": {},
                                "gold": {},
                                "status": "API retry limit exceeded",
                                "violated_constraint": {},
                                "is_exact_match": False,
                                "constraints_satisfied": False,
                                "pass_number": pass_num
                            }
                            with open(f"{pass_output_dir}/evaluation.json", "w") as f:
                                json.dump(error_eval_result, f, indent=4)
                            return
                        await asyncio.sleep(5)
                        try:
                            ai = initialize_model(model, keys)
                            logging.info(f"[{example_id}] Model reinitialized after error")
                        except Exception as init_error:
                            logging.error(f"[{example_id}] Failed to reinitialize model: {str(init_error)}")
                            # Save error evaluation result
                            error_eval_result = {
                                "has_execution_error": True,
                                "execution_output": f"Model reinitialization failed: {str(init_error)}",
                                "pred": {},
                                "gold": {},
                                "status": "Model reinitialization error",
                                "violated_constraint": {},
                                "is_exact_match": False,
                                "constraints_satisfied": False,
                                "pass_number": pass_num
                            }
                            with open(f"{pass_output_dir}/evaluation.json", "w") as f:
                                json.dump(error_eval_result, f, indent=4)
                            return
                
                api_call_time = time.time() - api_call_start
                logging.info(f"[{example_id}] Pass {pass_num} API call completed - {api_call_time:.2f}s")
                
                # Add to conversation history
                conversation_history.append({"role": "user", "content": current_prompt})
                conversation_history.append({"role": "assistant", "content": response_txt})
                
                # Save conversation
                save_start = time.time()
                with open(f"{pass_output_dir}/conversation.json", "w") as f:
                    json.dump(conversation_history, f, indent=4)
                
                # Extract and save code
                code_extract_start = time.time()
                generated_code = extract_code(response_txt)
                if not generated_code:
                    logging.error(f"[{example_id}] No code found in model response")
                    # Save error evaluation result
                    error_eval_result = {
                        "has_execution_error": True,
                        "execution_output": "No code found in model response",
                        "pred": {},
                        "gold": gold_formatted,
                        "status": "No code extracted",
                        "violated_constraint": {},
                        "is_exact_match": False,
                        "constraints_satisfied": False,
                        "pass_number": pass_num
                    }
                    with open(f"{pass_output_dir}/evaluation.json", "w") as f:
                        json.dump(error_eval_result, f, indent=4)
                    # Prepare feedback for next iteration instead of returning
                    current_prompt = f"Code extraction from the previous response failed. Please provide a complete Python solution using the Z3 solver. Make sure to surround your final code with ```python\nYOUR_CODE\n```.\n\nOriginal problem:\n{example['prompt_0shot']}"
                    continue
                    
                code_path = f"{pass_output_dir}/solution.py"
                with open(code_path, "w") as f:
                    f.write(generated_code)
                code_extract_time = time.time() - code_extract_start
                logging.info(f"[{example_id}] Pass {pass_num} code extracted and saved - {code_extract_time:.2f}s")
                
                # Execute code
                execution_start = time.time()
                execution_output = execute_python_code(code_path)
                execution_time = time.time() - execution_start
                logging.info(f"[{example_id}] Pass {pass_num} code execution - {execution_time:.2f}s")
                
                with open(f"{pass_output_dir}/output.out", "w") as f:
                    f.write(execution_output)
                save_time = time.time() - save_start
                logging.info(f"[{example_id}] Pass {pass_num} files saved - {save_time:.2f}s")
                
                # Check if execution had errors
                has_execution_error = ("Error" in execution_output or 
                                     "Exception" in execution_output or 
                                     "Traceback" in execution_output or
                                     not execution_output.strip())
                
                if has_execution_error:
                    logging.warning(f"[{example_id}] Pass {pass_num} execution error: {execution_output}")
                    # Save evaluation result with empty prediction
                    eval_result = {
                        "has_execution_error": True,
                        "execution_output": execution_output,
                        "pred": {},
                        "gold": gold_formatted,
                        "status": "Error",
                        "violated_constraint": {},
                        "is_exact_match": False,
                        "constraints_satisfied": False,
                        "pass_number": pass_num
                    }
                    with open(f"{pass_output_dir}/evaluation.json", "w") as f:
                        json.dump(eval_result, f, indent=4)
                    # Prepare feedback for next iteration
                    current_prompt = f"The previous code had the following error:\n{execution_output}\n\nPlease fix the code and provide a corrected version. Make sure to surround your final code with ```python\nYOUR_CODE\n```."
                    continue
                
                # Extract structured answer from execution output
                pred_extract_start = time.time()
                try:
                    # Determine whether to skip extract_answer based on task and arguments
                    if task == "trip":
                        # For trip tasks: default to skip, but can be overridden
                        should_skip_extract = not args.use_extract
                    else:
                        # For other tasks: default to use extract_answer, unless --skip_extract is specified
                        should_skip_extract = args.skip_extract
                    
                    if should_skip_extract:
                        # Try to parse JSON directly from execution output
                        logging.info(f"[{example_id}] Pass {pass_num} using execution output JSON directly for {task} task")
                        try:
                            # Try to find JSON in the execution output - use a simpler approach
                            import re
                            # Look for the first complete JSON object
                            json_match = re.search(r'\{[^{}]*(?:\{[^{}]*\}[^{}]*)*\}', execution_output, re.DOTALL)
                            if json_match:
                                pred_formatted = json.loads(json_match.group())
                                logging.info(f"[{example_id}] Pass {pass_num} successfully parsed JSON from execution output")
                            else:
                                logging.warning(f"[{example_id}] Pass {pass_num} no JSON found in execution output, using extract_answer")
                                pred_formatted = extract_answer(execution_output, task)
                        except (json.JSONDecodeError, KeyError) as e:
                            logging.warning(f"[{example_id}] Pass {pass_num} failed to parse JSON from execution output: {e}, falling back to extract_answer")
                            pred_formatted = extract_answer(execution_output, task)
                    else:
                        # Use the normal extract_answer process
                        pred_formatted = extract_answer(execution_output, task)
                    logging.info(f"[{example_id}] Pass {pass_num} extracted prediction: {pred_formatted}")
                except Exception as e:
                    logging.error(f"[{example_id}] Pass {pass_num} failed to extract prediction: {str(e)}")
                    pred_formatted = {}
                
                # Get gold answer
                gold = example["golden_plan"]
                if isinstance(gold, list):
                    gold = "\n".join(gold)
                try:
                    gold_formatted = extract_answer(gold, task)
                    logging.info(f"[{example_id}] Pass {pass_num} extracted gold: {gold_formatted}")
                except Exception as e:
                    logging.error(f"[{example_id}] Pass {pass_num} failed to extract gold: {str(e)}")
                    gold_formatted = {}
                
                # Evaluate constraints
                constraint_eval_start = time.time()
                eval_func = eval_functions[task]
                
                # Special handling for meeting task
                if task == "meeting":
                    num_people_to_meet = len(gold_formatted.get("itinerary", []))
                    constraints["num_people_to_meet"] = num_people_to_meet
                
                constraints_satisfied, violated_constraints = eval_func(constraints, pred_formatted)
                constraint_eval_time = time.time() - constraint_eval_start
                logging.info(f"[{example_id}] Pass {pass_num} constraint evaluation - {constraint_eval_time:.2f}s")
                logging.info(f"[{example_id}] Pass {pass_num} constraints satisfied: {constraints_satisfied}")
                if violated_constraints:
                    logging.info(f"[{example_id}] Pass {pass_num} violated constraints: {violated_constraints}")
                
                # Check exact match
                if task == "trip":
                    # For trip tasks, normalize both prediction and gold before comparison
                    normalized_pred = normalize_trip_itinerary(pred_formatted)
                    normalized_gold = normalize_trip_itinerary(gold_formatted)
                    is_exact_match = normalized_pred == normalized_gold
                else:
                    is_exact_match = pred_formatted == gold_formatted
                logging.info(f"[{example_id}] Pass {pass_num} exact match: {is_exact_match}")
                
                # Determine status
                status = "Correct" if constraints_satisfied else "Wrong plan"
                
                # Save evaluation result
                eval_result = {
                    "has_execution_error": False,
                    "execution_output": execution_output,
                    "pred": pred_formatted,
                    "gold": gold_formatted,
                    "status": status,
                    "violated_constraint": violated_constraints,
                    "is_exact_match": is_exact_match,
                    "constraints_satisfied": constraints_satisfied,
                    "pass_number": pass_num
                }
                with open(f"{pass_output_dir}/evaluation.json", "w") as f:
                    json.dump(eval_result, f, indent=4)
                
                if constraints_satisfied:
                    logging.info(f"[{example_id}] SUCCESS! Solved in pass {pass_num}")
                    return
                else:
                    logging.info(f"[{example_id}] Pass {pass_num} failed constraints, preparing feedback")
                    # Prepare feedback for next iteration
                    constraint_feedback = format_constraint_feedback(violated_constraints, task)
                    current_prompt = f"The previous solution produced the following output:\n{execution_output}\n{constraint_feedback}\n\nPlease revise your solution to satisfy these constraints. Make sure to surround your final code with ```python\nYOUR_CODE\n```."
            
            logging.warning(f"[{example_id}] FAILED to solve within {max_passes} passes")
            
            # Save final evaluation result even if we failed to solve
            if 'pred_formatted' in locals() and 'gold_formatted' in locals():
                # Determine the correct status based on what happened in the last pass
                if has_execution_error:
                    # Check if it's a code extraction error specifically
                    if execution_output == "No code found in model response":
                        final_status = "No code extracted"
                    else:
                        final_status = "Error"
                elif not constraints_satisfied:
                    final_status = "Wrong plan"
                else:
                    final_status = "Failed to solve within max passes"
                
                final_eval_result = {
                    "has_execution_error": has_execution_error,
                    "execution_output": execution_output,
                    "pred": pred_formatted,
                    "gold": gold_formatted,
                    "status": final_status,
                    "violated_constraint": violated_constraints,
                    "is_exact_match": is_exact_match,
                    "constraints_satisfied": constraints_satisfied,
                    "pass_number": pass_num
                }
                with open(f"{pass_output_dir}/evaluation.json", "w") as f:
                    json.dump(final_eval_result, f, indent=4)
                logging.info(f"[{example_id}] Saved final evaluation result from pass {pass_num} with status: {final_status}")
            
            return
            
        except Exception as e:
            logging.error(f"[{example_id}] Unexpected error: {str(e)}")
            # Save error evaluation result
            try:
                error_eval_result = {
                    "has_execution_error": True,
                    "execution_output": f"Unexpected error: {str(e)}",
                    "pred": {},
                    "gold": {},
                    "status": "Unexpected error",
                    "violated_constraint": {},
                    "is_exact_match": False,
                    "constraints_satisfied": False,
                    "pass_number": 0
                }
                # Try to save to first pass directory, create if needed
                first_pass_dir = f"{output_dir}/1_pass"
                os.makedirs(first_pass_dir, exist_ok=True)
                with open(f"{first_pass_dir}/evaluation.json", "w") as f:
                    json.dump(error_eval_result, f, indent=4)
                logging.info(f"[{example_id}] Saved error evaluation result")
            except Exception as save_error:
                logging.error(f"[{example_id}] Failed to save error evaluation: {str(save_error)}")
            return

async def main():
    """Main function to run the iterative refinement process"""
    args = parse_args()
    
    # Set up logging
    logging.basicConfig(
        level=logging.INFO,
        format='%(asctime)s - %(levelname)s - %(message)s',
        datefmt='%Y-%m-%d %H:%M:%S'
    )
    
    # Task prefix mapping
    task_prefix_map = {
        "calendar": "calendar_scheduling",
        "trip": "trip_planning",
        "meeting": "meeting_planning"
    }
    
    logging.info(f"Starting model: {args.model} with {args.max_concurrent} concurrent examples")
    logging.info(f"Starting task: {args.task}")
    
    # Load examples and constraints
    examples = load_examples(args.task)
    constraints = load_constraints(args.task)
    
    # Process specific examples if provided
    if args.examples:
        logging.info(f"Processing specific examples: {args.examples}")
        try:
            # Split and convert to integers, with extra cleaning
            example_numbers = [int(num.strip()) for num in args.examples.split(",") if num.strip()]
            logging.info(f"Parsed example numbers: {example_numbers}")
            
            # Filter examples to only include specified numbers
            task_prefix = task_prefix_map[args.task]
            example_ids = [f"{task_prefix}_example_{num}" for num in example_numbers]
            examples = {example_id: examples[example_id] for example_id in example_ids if example_id in examples}
            
            if not examples:
                logging.error("No valid examples found in the specified range")
                return
                
            # Clear output directories for specified examples
            for example_id in examples:
                output_dir = f"../output/SMT/{args.model}/{args.task}/n_pass/{example_id}"
                if os.path.exists(output_dir):
                    logging.info(f"Clearing output directory for {example_id}")
                    shutil.rmtree(output_dir)
        except ValueError as e:
            logging.error(f"Error parsing example numbers: {e}")
            logging.error(f"Raw examples string: '{args.examples}'")
            return
    
    # Filter examples by start/end range if specified
    if args.start is not None or args.end is not None:
        logging.info(f"Filtering examples: start={args.start}, end={args.end}")
        # Convert examples dict to list of (example_id, example) tuples and slice
        examples_list = list(examples.items())
        start_idx = args.start if args.start is not None else 0
        end_idx = args.end if args.end is not None else len(examples_list)
        
        # Slice the examples list
        filtered_examples_list = examples_list[start_idx:end_idx]
        examples = dict(filtered_examples_list)
        logging.info(f"Filtered to {len(examples)} examples (indices {start_idx} to {end_idx-1})")
    
    rate_limiter = RateLimiter(args.rate_limit)
    semaphore = asyncio.Semaphore(args.max_concurrent)
    
    # Process examples
    tasks = []
    for example_id, example in examples.items():
        task = asyncio.create_task(
            process_single_example(
                example_id,
                example,
                constraints.get(example_id, {}),
                args.model,
                args.max_passes,
                rate_limiter,
                semaphore,
                args.task,
                args
            )
        )
        tasks.append(task)
    
    # Wait for all tasks to complete
    results = await asyncio.gather(*tasks, return_exceptions=True)
    
    # Log results
    success_count = sum(1 for r in results if not isinstance(r, Exception))
    error_count = len(results) - success_count
    logging.info(f"Completed processing {len(results)} examples: {success_count} successful, {error_count} failed")

def load_examples(task):
    """Load examples from the appropriate JSON file"""
    task_name_map = {
        "calendar": "calendar_scheduling",
        "trip": "trip_planning",
        "meeting": "meeting_planning"
    }
    with open(f"../data/{task_name_map[task]}_100.json") as f:
        return json.load(f)

def load_constraints(task):
    """Load constraints from the appropriate JSON file"""
    task_name_map = {
        "calendar": "calendar_scheduling",
        "trip": "trip_planning",
        "meeting": "meeting_planning"
    }
    with open(f"../data/{task_name_map[task]}_100_constraints.json") as f:
        constraints_data = json.load(f)
        return {example_id: data.get("constraints", {}) 
                for example_id, data in constraints_data.items()}

if __name__ == "__main__":
    asyncio.run(main()) 