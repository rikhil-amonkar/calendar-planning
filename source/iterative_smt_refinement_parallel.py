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

# Configure logging for timestamps
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    datefmt='%Y-%m-%d %H:%M:%S'
)

# Argument parsing
parser = argparse.ArgumentParser(
    description="Parallel Iterative SMT refinement with constraint feedback",
    formatter_class=argparse.RawDescriptionHelpFormatter,
    epilog="""
Examples:
  # Run calendar scheduling with 5 concurrent examples
  python iterative_smt_refinement_parallel.py --task calendar --model DeepSeek-R1 --start 0 --end 10 --max_passes 3 --max_concurrent 5
  
  # Run with rate limiting (2 requests per second)
  python iterative_smt_refinement_parallel.py --task all --model gpt-4o-mini --rate_limit 2.0
"""
)
parser.add_argument('--task', choices=['calendar', 'trip', 'meeting', 'all'], required=True, 
                   help="Task to run")
parser.add_argument('--model', required=True, nargs='+', 
                   help="Model(s) to use")
parser.add_argument('--fresh', action='store_true', 
                   help="Re-run all examples, ignoring existing successful solutions")
parser.add_argument('--start', type=int, default=0, 
                   help="Starting index for processing examples")
parser.add_argument('--end', type=int, default=-1, 
                   help="Ending index for processing examples")
parser.add_argument('--max_passes', type=int, default=5, 
                   help="Maximum number of refinement passes per example")
parser.add_argument('--max_concurrent', type=int, default=20,
                   help="Maximum number of examples to process concurrently")
parser.add_argument('--rate_limit', type=float, default=1.0,
                   help="Requests per second limit (to avoid API rate limits)")
args = parser.parse_args()

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
    
    prompt = {
        "calendar": "Given the following time range:\n" + answer_str + "\nExtract the meeting start day and time in a JSON like {\"day\": \"Monday\", \"start_time\": \"14:30\", \"end_time\": \"15:30\"}. The time should be in 24-hour format. If no time range is given at all, output an empty JSON.",
        "trip": "Given the following itinerary:\n" + answer_str + "\nExtract the days spent in each city in a JSON format like {\"itinerary\": [{\"day_range\": \"Day 1-2\", \"place\": \"Reykjavik\"}, {\"day_range\": \"Day 2-4\", \"place\": \"Stockholm\"}......]}. Only keep the days in a city. If flying from city A to city B, that day should be included in both ranges for both cites. The day range should be inclusive. For example, arrving at Reykjavik in Day 1 and flying to Stockholm on Day 2 will result in the dictionary above. If no itinerary is given, output an empty JSON.",
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
    model_name: str,
    model_short_name: str,
    task: str,
    example_id: str,
    example: Dict,
    example_constraints: Dict,
    rate_limiter: RateLimiter,
    semaphore: asyncio.Semaphore
) -> Dict[str, Any]:
    """Process a single example with iterative refinement"""
    
    example_start_time = time.time()
    async with semaphore:  # Limit concurrent examples
        logging.info(f"[{example_id}] Starting processing")
        
        # Check if we should skip this example
        skip_check_start = time.time()
        base_output_dir = f"../output/SMT/{model_short_name}/{task}/n_pass/{example_id}"
        if not args.fresh and os.path.exists(base_output_dir):
            # Check if we already have a successful solution
            for pass_num in range(1, args.max_passes + 1):
                eval_path = f"{base_output_dir}/{pass_num}_pass/evaluation.json"
                if os.path.exists(eval_path):
                    with open(eval_path, 'r') as f:
                        eval_data = json.load(f)
                        if eval_data.get("constraints_satisfied", False):
                            skip_check_time = time.time() - skip_check_start
                            logging.info(f"[{example_id}] Skipped (existing solution in pass {pass_num}) - {skip_check_time:.2f}s")
                            return {"example_id": example_id, "status": "skipped", "pass": pass_num, "total_time": skip_check_time}

        # Initialize AI model for this example
        model_init_start = time.time()
        ai = initialize_model(model_name, keys)
        model_init_time = time.time() - model_init_start
        logging.info(f"[{example_id}] Model initialized - {model_init_time:.2f}s")
        
        # Initialize conversation history
        conversation_history = []
        
        # Initial prompt
        prompt_prep_start = time.time()
        initial_prompt = "Given the following scheduling problem:\n"
        initial_prompt += f"{example['prompt_0shot']}\n"
        if task == "calendar":
            initial_prompt += "Your solution should always have three things: the day to meet, the start time, and the end time.\n"
        if task == "trip":
            initial_prompt += "Note that if one flies from city A to city B on day X, then they are in both cities A and B on day X, which contributes to the total number of days in each city.\n"
        initial_prompt += "Write a Python program that solves it using the Z3 solver. Always surround your final code with ```python\nYOUR_CODE\n```.\n"
        
        current_prompt = initial_prompt
        prompt_prep_time = time.time() - prompt_prep_start
        logging.info(f"[{example_id}] Prompt prepared - {prompt_prep_time:.2f}s")
        
        for pass_num in range(1, args.max_passes + 1):
            pass_start_time = time.time()
            logging.info(f"[{example_id}] Starting pass {pass_num}")
            
            # Create output directory for this pass
            dir_create_start = time.time()
            pass_output_dir = f"{base_output_dir}/{pass_num}_pass"
            os.makedirs(pass_output_dir, exist_ok=True)
            dir_create_time = time.time() - dir_create_start
            
            # Get response from model with rate limiting
            api_call_start = time.time()
            retry_count = 0
            max_retries = 3
            while retry_count < max_retries:
                try:
                    response_txt = await run_model_with_rate_limit(ai, current_prompt, rate_limiter)
                    break
                except Exception as e:
                    retry_count += 1
                    logging.warning(f"[{example_id}] API error in pass {pass_num} (attempt {retry_count}): {e}")
                    if retry_count >= max_retries:
                        total_time = time.time() - example_start_time
                        return {"example_id": example_id, "status": "api_error", "error": str(e), "total_time": total_time}
                    await asyncio.sleep(5)
                    ai = initialize_model(model_name, keys)
            
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
            code_path = f"{pass_output_dir}/solution.py"
            with open(code_path, "w") as f:
                f.write(generated_code)
            code_extract_time = time.time() - code_extract_start
            
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
            
            # Extract gold plan
            gold_extract_start = time.time()
            gold = example["golden_plan"]
            if isinstance(gold, list):
                gold = "\n".join(gold)
            try:
                gold_formatted = extract_answer(gold, task)
            except Exception as e:
                gold_formatted = {}
            gold_extract_time = time.time() - gold_extract_start
            
            if has_execution_error:
                logging.warning(f"[{example_id}] Pass {pass_num} execution error, preparing feedback")
                # Prepare feedback for next iteration
                current_prompt = f"The previous code had the following error:\n{execution_output}\n\nPlease fix the code and provide a corrected version. Make sure to surround your final code with ```python\nYOUR_CODE\n```."
                
                # Save evaluation indicating execution error
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
                
                pass_time = time.time() - pass_start_time
                logging.info(f"[{example_id}] Pass {pass_num} completed (error) - {pass_time:.2f}s")
                continue
            
            # Extract structured answer from execution output
            pred_extract_start = time.time()
            try:
                pred_formatted = extract_answer(execution_output, task)
            except Exception as e:
                pred_formatted = {}
            pred_extract_time = time.time() - pred_extract_start
            
            # Evaluate constraints
            constraint_eval_start = time.time()
            eval_func = eval_functions[task]
            
            # Special handling for meeting task
            if task == "meeting":
                num_people_to_meet = len(gold_formatted.get("itinerary", []))
                example_constraints["num_people_to_meet"] = num_people_to_meet
            
            constraints_satisfied, violated_constraints = eval_func(example_constraints, pred_formatted)
            constraint_eval_time = time.time() - constraint_eval_start
            logging.info(f"[{example_id}] Pass {pass_num} constraint evaluation - {constraint_eval_time:.2f}s")
            
            # Check exact match
            is_exact_match = pred_formatted == gold_formatted
            
            # Determine status
            status = "Correct" if constraints_satisfied else "Wrong plan"
            
            # Save evaluation result
            eval_save_start = time.time()
            eval_result = {
                "has_execution_error": False,
                "execution_output": execution_output,
                "pred": pred_formatted,
                "gold": gold_formatted,
                "status": status,
                "violated_constraint": violated_constraints,
                "is_exact_match": is_exact_match,
                "constraints_satisfied": constraints_satisfied,
                "pass_number": pass_num,
                "timing": {
                    "api_call_time": api_call_time,
                    "execution_time": execution_time,
                    "constraint_eval_time": constraint_eval_time,
                    "pred_extract_time": pred_extract_time,
                    "gold_extract_time": gold_extract_time
                }
            }
            with open(f"{pass_output_dir}/evaluation.json", "w") as f:
                json.dump(eval_result, f, indent=4)
            eval_save_time = time.time() - eval_save_start
            
            pass_time = time.time() - pass_start_time
            
            if constraints_satisfied:
                total_time = time.time() - example_start_time
                logging.info(f"[{example_id}] SUCCESS! Solved in pass {pass_num} - Pass: {pass_time:.2f}s, Total: {total_time:.2f}s")
                return {"example_id": example_id, "status": "success", "pass": pass_num, "total_time": total_time}
            else:
                logging.info(f"[{example_id}] Pass {pass_num} failed constraints - {pass_time:.2f}s")
                # Prepare feedback for next iteration
                constraint_feedback = format_constraint_feedback(violated_constraints, task)
                current_prompt = f"The previous solution produced the following output:\n{execution_output}\n{constraint_feedback}\n\nPlease revise your solution to satisfy these constraints. Make sure to surround your final code with ```python\nYOUR_CODE\n```."
        
        total_time = time.time() - example_start_time
        logging.warning(f"[{example_id}] FAILED to solve within {args.max_passes} passes - Total: {total_time:.2f}s")
        return {"example_id": example_id, "status": "failed", "max_passes": args.max_passes, "total_time": total_time}

async def main():
    """Main execution function with parallel processing"""
    rate_limiter = RateLimiter(args.rate_limit)
    semaphore = asyncio.Semaphore(args.max_concurrent)
    
    for model_name in args.model:
        model_start_time = time.time()
        model_short_name = model_name.split("/")[-1] if "/" in model_name else model_name
        logging.info(f"Starting model: {model_name} with {args.max_concurrent} concurrent examples")

        if args.task == "all":
            tasks = ["calendar", "trip", "meeting"]
        else:
            tasks = [args.task]

        for task in tasks:
            task_start_time = time.time()
            logging.info(f"Starting task: {task}")
            
            # Load data and constraints
            data_load_start = time.time()
            with open(f"../data/{task_name_map[task]}_100.json") as f:
                data = json.load(f)
            
            with open(f"../data/{task_name_map[task]}_100_constraints.json") as f:
                constraints_data = json.load(f)
            data_load_time = time.time() - data_load_start
            logging.info(f"Data loaded for {task} - {data_load_time:.2f}s")

            # Prepare examples to process
            prep_start_time = time.time()
            examples_to_process = []
            for idx, (example_id, example) in enumerate(data.items()):
                if idx < args.start or (args.end != -1 and idx >= args.end):
                    continue
                
                example_constraints = constraints_data.get(example_id, {}).get("constraints", {})
                examples_to_process.append((example_id, example, example_constraints))
            prep_time = time.time() - prep_start_time
            
            logging.info(f"Processing {len(examples_to_process)} examples concurrently - Prep: {prep_time:.2f}s")
            
            # Create tasks for parallel processing
            task_create_start = time.time()
            tasks_list = [
                process_single_example(
                    model_name, model_short_name, task, 
                    example_id, example, example_constraints,
                    rate_limiter, semaphore
                )
                for example_id, example, example_constraints in examples_to_process
            ]
            task_create_time = time.time() - task_create_start
            logging.info(f"Created {len(tasks_list)} async tasks - {task_create_time:.2f}s")
            
            # Execute all tasks concurrently
            execution_start_time = time.time()
            logging.info(f"Starting concurrent execution of {len(tasks_list)} examples...")
            results = await asyncio.gather(*tasks_list, return_exceptions=True)
            execution_end_time = time.time()
            execution_time = execution_end_time - execution_start_time
            
            # Calculate detailed statistics
            success_results = [r for r in results if isinstance(r, dict) and r.get("status") == "success"]
            failed_results = [r for r in results if isinstance(r, dict) and r.get("status") == "failed"]
            error_results = [r for r in results if isinstance(r, Exception) or (isinstance(r, dict) and r.get("status") == "api_error")]
            skipped_results = [r for r in results if isinstance(r, dict) and r.get("status") == "skipped"]
            
            success_count = len(success_results)
            failed_count = len(failed_results)
            error_count = len(error_results)
            skipped_count = len(skipped_results)
            
            # Calculate timing statistics
            if success_results:
                success_times = [r.get("total_time", 0) for r in success_results if r.get("total_time")]
                avg_success_time = sum(success_times) / len(success_times) if success_times else 0
                min_success_time = min(success_times) if success_times else 0
                max_success_time = max(success_times) if success_times else 0
            else:
                avg_success_time = min_success_time = max_success_time = 0
            
            task_total_time = time.time() - task_start_time
            
            # Log comprehensive summary
            logging.info(f"=== TASK {task.upper()} COMPLETED ===")
            logging.info(f"Total time: {task_total_time:.2f}s (Execution: {execution_time:.2f}s)")
            logging.info(f"Results: {success_count} success, {failed_count} failed, {error_count} errors, {skipped_count} skipped")
            if success_results:
                logging.info(f"Success timing - Avg: {avg_success_time:.2f}s, Min: {min_success_time:.2f}s, Max: {max_success_time:.2f}s")
            logging.info(f"Throughput: {len(examples_to_process)/execution_time:.2f} examples/second")
            
            # Log any errors
            for i, result in enumerate(results):
                if isinstance(result, Exception):
                    example_id = examples_to_process[i][0]
                    logging.error(f"Exception in {example_id}: {result}")
                elif isinstance(result, dict) and result.get("status") == "api_error":
                    logging.error(f"API error in {result['example_id']}: {result.get('error', 'Unknown')}")

if __name__ == "__main__":
    asyncio.run(main()) 