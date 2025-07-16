"""
Enhanced Iterative SMT Refinement with Smart Code Extraction and Execution Handling

This script implements an iterative refinement process for solving scheduling problems using Z3 SMT solver.
It uses GPT for intelligent code extraction and execution result parsing, with comprehensive error handling.

Features:
1. Smart code extraction using GPT even when code blocks aren't properly formatted
2. Intelligent execution result parsing and formatting using GPT
3. Comprehensive error handling for different failure scenarios
4. Parallel processing with rate limiting
5. Detailed feedback generation for different error types

Directory structure for outputs:
../output/SMT/{model_name}/{task}/n_pass/{example_id}/{pass_number}_pass/
  - conversation.json: Full conversation history
  - solution.py: Generated Z3 code
  - output.out: Execution output
  - evaluation.json: Constraint evaluation results

Usage:
python iterative_smt_refinement_enhanced.py --task calendar --model DeepSeek-V3 --start 0 --end 5
python iterative_smt_refinement_enhanced.py --task trip --model gpt-4o-mini --examples '1009,1010'
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
from openai import OpenAI

import torch
torch.cuda.empty_cache()  # Clear cache
torch.backends.cudnn.benchmark = False  # Reduce memory usage

# Configure logging for timestamps
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    datefmt='%Y-%m-%d %H:%M:%S'
)

def parse_args():
    """Parse command line arguments"""
    parser = argparse.ArgumentParser(description="Run enhanced iterative SMT refinement with smart extraction")
    parser.add_argument("--model", type=str, required=True, help="Model to use (e.g., 'DeepSeek-R1')")
    parser.add_argument("--task", type=str, required=True, choices=["calendar", "trip", "meeting"], help="Task type")
    parser.add_argument("--max_passes", type=int, default=5, help="Maximum number of refinement passes")
    parser.add_argument("--max_concurrent", type=int, default=10, help="Maximum number of concurrent examples to process")
    parser.add_argument("--rate_limit", type=int, default=60, help="Rate limit (requests per minute)")
    parser.add_argument("--start", type=int, help="Start example number (inclusive)")
    parser.add_argument("--end", type=int, help="End example number (exclusive)")
    parser.add_argument("--fresh", action="store_true", help="Clear all output directories before running")
    parser.add_argument("--examples", type=str, help="Comma-separated list of example numbers to run (e.g., '25,35')")
    
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
        prompt = f"""Extract the Python code from the following text. Look for any Python code that might solve a scheduling problem using Z3 solver.

Text:
{response_txt}

If you find Python code, return ONLY the code without any markdown formatting or explanations.
If no Python code is found, return an empty string.

Focus on:
1. Code that imports and uses Z3 solver
2. Code that defines variables, constraints, and solves problems
3. Code that prints or returns results

Return only the Python code:"""

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
        
        prompt = f"""Extract structured data from the following execution output for a {task} planning task.

Execution Output:
{execution_output}

Expected format: {expected_format}

Instructions:
1. If the output contains valid JSON in the expected format, extract and return it
2. If the output indicates no plan was found (like "No valid itinerary found", "No solution found", "UNSAT", "unsat", etc.), return {{"no_plan": "reason"}}
3. If the output contains an execution error message (like "Error:", "Exception:", "Traceback:", etc.), return {{"error": "error_message"}}
4. If the output is malformed or unclear, try to extract any useful information or return {{"error": "malformed_output"}}

Return only valid JSON:"""

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

def extract_answer_basic(answer_str, task):
    """Basic extraction fallback - same as original script"""
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
    
    # For trip task, use the revised format and instructions
    prompt = {
        "calendar": "Given the following time range:\n" + answer_str + "\nExtract the meeting start day and time in a JSON like {\"day\": \"Monday\", \"start_time\": \"14:30\", \"end_time\": \"15:30\"}. The time should be in 24-hour format. If no time range is given at all, output an empty JSON.",
        "trip": (
            "Given the following itinerary:\n" + answer_str +
            "\nExtract the days spent in each city in a JSON format like "
            "{\"itinerary\": [{\"day_range\": \"Day 1-4\", \"place\": \"Tallinn\"}, {\"day_range\": \"Day 4-6\", \"place\": \"Munich\"}]}. "
            "Each entry should represent a continuous stay in a city, with the day range inclusive. "
            "IMPORTANT: When you fly from city A to city B on day X, that day counts for BOTH cities. "
            "For example:\n"
            "- If you stay in Venice from Day 1-3 and fly to Vienna on Day 3, then:\n"
            "  - Venice: Day 1-3 (3 days)\n"
            "  - Vienna: Day 3-6 (4 days, including the flight day)\n"
            "- The flight day (Day 3) is counted for both Venice and Vienna.\n"
            "- Do NOT create separate flight entries in the JSON.\n"
            "If no itinerary is given, output an empty JSON."
        ),
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

# Build evaluation functions directly in this file
def execute_python_code(code_path):
    """Execute Python code and return the output"""
    try:
        result = subprocess.run(['python3', code_path], capture_output=True, text=True, timeout=30)
        return result.stdout + result.stderr
    except subprocess.TimeoutExpired:
        return "Execution timeout"
    except Exception as e:
        return f"Execution error: {str(e)}"

def format_constraint_feedback(violated_constraints):
    """Format constraint violations into feedback"""
    if not violated_constraints:
        return ""
    
    feedback = "The following constraints are violated:\n"
    for constraint, details in violated_constraints.items():
        feedback += f"- {constraint}: {details}\n"
    return feedback

def evaluate_calendar(constraints, pred_dict):
    # Check for missing day, start_time, or end_time
    if not pred_dict or "day" not in pred_dict or "start_time" not in pred_dict or "end_time" not in pred_dict:
        return False, {"missing_fields": True}
    
    pred_day = pred_dict["day"]
    pred_start = pred_dict["start_time"]
    pred_end = pred_dict["end_time"]
    
    # Check for None values in any of the fields
    if pred_day is None or pred_start is None or pred_end is None:
        return False, {"null_fields": True}
    
    # Convert time strings to numerical values
    if isinstance(pred_start, str):
        pred_start_parts = pred_start.split(":")
        try:
            pred_start = float(pred_start_parts[0]) + float(pred_start_parts[1]) / 60
        except ValueError:
            return False, {"unparsable": True}
    if isinstance(pred_end, str):
        pred_end_parts = pred_end.split(":")
        try:
            pred_end = float(pred_end_parts[0]) + float(pred_end_parts[1]) / 60
        except ValueError:
            return False, {"unparsable": True}
    meeting_duration = constraints.get("meeting_duration")
    if meeting_duration is None:
        return False, {"missing_meeting_duration": True}
    if (pred_end - pred_start) != meeting_duration:
        return False, {"meeting_duration": meeting_duration}
    for disallowed_range in constraints.get("disallowed_ranges", []):
        if disallowed_range["day"] == pred_day:
            if (pred_start >= disallowed_range["start"] and pred_start < disallowed_range["end"]) or \
               (pred_end > disallowed_range["start"] and pred_end <= disallowed_range["end"]) or \
               (pred_start <= disallowed_range["start"] and pred_end >= disallowed_range["end"]):
                return False, disallowed_range
    return True, {}

def evaluate_trip(constraints, pred_dict):
    # parse the predicted itinerary segments
    segments = []
    for seg in pred_dict["itinerary"]:
        # Handle special cases like "Day {current_day}-{current_day + 2}"
        if not seg["day_range"].startswith("Day ") or "{" in seg["day_range"] or "}" in seg["day_range"]:
            return False, {"invalid_day_range_format": seg["day_range"]}
        # "Day X-Y"
        dr = seg["day_range"].replace("Day ", "")
        if "-" in dr:
            start_s, end_s = dr.split("-")
        else:
            start_s, end_s = [dr, dr]
        try:
            start, end = int(start_s), int(end_s)
        except ValueError:
            return False, {"unparsable_day_range": seg["day_range"]}
        segments.append({"place": seg["place"], "start": start, "end": end})
    
    # Sort segments by start day to ensure chronological order for constraint evaluation
    segments.sort(key=lambda x: x["start"])
    
    # 1) check full coverage from day 1 to total_days, with no gaps/overlaps
    total = constraints.get("trip_length")
    if not segments or segments[0]["start"] != 1 or segments[-1]["end"] != total:
        return False, {"total_days": total}
    for a, b in zip(segments, segments[1:]):
        if a["end"] != b["start"]:
            return False, {"gap/overlap": (a, b)}
    # 2) check each place's stay duration
    for seg in segments:
        required = constraints.get("stay_days", {}).get(seg["place"])
        if required is not None:
            actual = seg["end"] - seg["start"] + 1
            if actual != required:
                return False, {"stay_days": {seg["place"]: required}}
    # 3) check event_ranges (must fall entirely within the visit segment)
    for ev in constraints.get("city_day_ranges", []):
        place = ev["city"]
        container = next((s for s in segments if s["place"] == place), None)
        if not container:
            return False, {"missing_place": place}
        if container["start"] > ev["start"] or container["end"] < ev["end"]:
            return False, {"event_range": ev}
    # 4) check flight connectivity between consecutive places
    allowed = [(d["from"], d["to"]) for d in constraints.get("direct_flights", [])]
    for a, b in zip(segments, segments[1:]):
        pair = (a["place"], b["place"])
        if pair not in allowed:
            return False, {"flight": {"from": a["place"], "to": b["place"]}}
    return True, {}

def evaluate_meeting(constraints, pred_dict):
    from datetime import datetime
    def parse_time(s):
        try:
            if s.endswith(("AM", "PM")):
                return datetime.strptime(s, "%I:%M%p")
            return datetime.strptime(s, "%H:%M")
        except ValueError:
            return None
    people = {p["name"]: p for p in constraints.get("people_to_meet", [])}
    start_location = constraints.get("start", {}).get("location")
    start_time = constraints.get("start", {}).get("time_of_day")
    
    # Calculate num_people_to_meet from people_to_meet array length
    num_people_to_meet = constraints.get("num_people_to_meet", len(constraints.get("people_to_meet", [])))
    
    meetings = []
    for m in pred_dict.get("itinerary", []):
        name = m["person"]
        start = parse_time(m["start_time"])
        end = parse_time(m["end_time"])
        if start is None or end is None:
            return False, {"invalid_time_format": {"start": m["start_time"], "end": m["end_time"]}}
        loc = people.get(name, {}).get("location")
        meetings.append({"person": name, "start": start, "end": end, "location": loc})
    if len(meetings) < num_people_to_meet:
        return False, {"num_people_to_meet": num_people_to_meet}
    meetings.sort(key=lambda x: x["start"])
    for m in meetings:
        p = people.get(m["person"])
        if not p:
            continue
        avail = p["time_of_day"]
        av_from = parse_time(avail["from"])
        av_to = parse_time(avail["to"])
        if m["start"] < av_from or m["end"] > av_to:
            return False, {"person": m["person"], "time_of_day": avail}
    travel = {}
    for d in constraints.get("travel_distances", []):
        pl = d["place"]
        frm = pl.get("from", constraints.get("start", {}).get("location"))
        to = pl["to"]
        travel[(frm, to)] = d["walking_time"]
    if start_time:
        st = parse_time(start_time)
        first = meetings[0]
        if first["start"] < st:
            return False, {"start_time": start_time}
        walk0 = travel.get((start_location, first["location"]))
        gap0 = (first["start"] - st).total_seconds() / 60
        if walk0 is not None and walk0 > gap0:
            return False, {
                "travel_start": {
                    "to_person": first["person"],
                    "to_location": first["location"],
                    "travel_time": walk0
                }
            }
    for a, b in zip(meetings, meetings[1:]):
        gap_mins = (b["start"] - a["end"]).total_seconds() / 60
        walk = travel.get((a["location"], b["location"]))
        if walk is not None and walk > gap_mins:
            return False, {
                "travel": {
                    "from_person": a["person"],
                    "to_person": b["person"],
                    "from_location": a["location"],
                    "to_location": b["location"],
                    "travel_time": walk
                }
            }
    return True, {}

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
    """Process a single example with enhanced error handling and smart feedback"""
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
                initial_prompt += "Do not include separate flight entries in the JSON output.\n"
                initial_prompt += "IMPORTANT: When you fly from city A to city B on day X, that day counts for BOTH cities. For example:\n"
                initial_prompt += "- If you stay in Venice from Day 1-3 and fly to Vienna on Day 3, then:\n"
                initial_prompt += "  - Venice: Day 1-3 (3 days)\n"
                initial_prompt += "  - Vienna: Day 3-6 (4 days, including the flight day)\n"
                initial_prompt += "- The flight day (Day 3) is counted for both Venice and Vienna.\n"
                initial_prompt += "- Do NOT create separate flight entries in the JSON.\n"
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
                
                # Extract and save code using smart extraction
                code_extract_start = time.time()
                generated_code = smart_extract_code(response_txt)
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
                    # Prepare feedback for next iteration
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
                
                # Extract structured answer from execution output using smart extraction
                pred_extract_start = time.time()
                try:
                    pred_formatted = smart_extract_execution_result(execution_output, task)
                    logging.info(f"[{example_id}] Pass {pass_num} extracted prediction: {pred_formatted}")
                except Exception as e:
                    logging.error(f"[{example_id}] Pass {pass_num} failed to extract prediction: {str(e)}")
                    pred_formatted = {}
                
                # Enhanced error handling for different execution scenarios
                execution_error = None
                no_plan_found = False
                
                # Check for execution errors
                if isinstance(pred_formatted, dict):
                    if "error" in pred_formatted:
                        execution_error = pred_formatted["error"]
                        logging.warning(f"[{example_id}] Pass {pass_num} execution error: {execution_error}")
                    elif "no_plan" in pred_formatted:
                        no_plan_found = True
                        logging.warning(f"[{example_id}] Pass {pass_num} no plan found: {pred_formatted['no_plan']}")
                
                # Get gold answer
                gold = example["golden_plan"]
                if isinstance(gold, list):
                    gold = "\n".join(gold)
                try:
                    gold_formatted = extract_answer_basic(gold, task)
                    logging.info(f"[{example_id}] Pass {pass_num} extracted gold: {gold_formatted}")
                except Exception as e:
                    logging.error(f"[{example_id}] Pass {pass_num} failed to extract gold: {str(e)}")
                    gold_formatted = {}
                
                # Evaluate constraints (only if we have a valid prediction)
                constraint_eval_start = time.time()
                eval_func = eval_functions[task]
                
                # Special handling for meeting task
                # Note: num_people_to_meet is calculated dynamically from people_to_meet array length
                # No need to add it to constraints
                
                if execution_error or no_plan_found:
                    # Skip constraint evaluation for errors
                    constraints_satisfied = False
                    violated_constraints = {}
                else:
                    constraints_satisfied, violated_constraints = eval_func(constraints, pred_formatted)
                
                constraint_eval_time = time.time() - constraint_eval_start
                logging.info(f"[{example_id}] Pass {pass_num} constraint evaluation - {constraint_eval_time:.2f}s")
                logging.info(f"[{example_id}] Pass {pass_num} constraints satisfied: {constraints_satisfied}")
                if violated_constraints:
                    logging.info(f"[{example_id}] Pass {pass_num} violated constraints: {violated_constraints}")
                
                # Check exact match (only if we have valid prediction)
                if not execution_error and not no_plan_found:
                    if task == "trip":
                        # For trip tasks, normalize both prediction and gold before comparison
                        normalized_pred = normalize_trip_itinerary(pred_formatted)
                        normalized_gold = normalize_trip_itinerary(gold_formatted)
                        is_exact_match = normalized_pred == normalized_gold
                    else:
                        is_exact_match = pred_formatted == gold_formatted
                else:
                    is_exact_match = False
                logging.info(f"[{example_id}] Pass {pass_num} exact match: {is_exact_match}")
                
                # Determine status and prepare feedback
                if execution_error:
                    status = f"Execution error: {execution_error}"
                elif no_plan_found:
                    status = f"No plan found: {pred_formatted.get('no_plan', 'Unknown reason')}"
                elif constraints_satisfied:
                    status = "Correct"
                else:
                    status = "Wrong plan"
                
                # Save evaluation result
                eval_result = {
                    "has_execution_error": bool(execution_error),
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
                
                # Check for success conditions
                if constraints_satisfied:
                    logging.info(f"[{example_id}] SUCCESS! Solved in pass {pass_num}")
                    return
                
                # Prepare enhanced feedback for next iteration based on different scenarios
                if execution_error:
                    # Scenario 3: Execution error - provide error message as feedback
                    logging.info(f"[{example_id}] Pass {pass_num} execution error, preparing error feedback")
                    current_prompt = f"The previous Z3 solution returned an error: {execution_error}\n\nPlease revise your Z3 program to fix this error. The error suggests there may be an issue with the Z3 code.\n\nMake sure to surround your final code with ```python\nYOUR_CODE\n```."
                
                elif no_plan_found:
                    # Scenario 4: No plan found - suggest adjusting solution
                    logging.info(f"[{example_id}] Pass {pass_num} no plan found, preparing no-plan feedback")
                    no_plan_reason = pred_formatted.get('no_plan', 'Unknown reason')
                    current_prompt = f"The previous Z3 solution failed to find a plan.\n\nPlease adjust your Z3 program to find a solution.\n\nMake sure to surround your final code with ```python\nYOUR_CODE\n```."
                
                else:
                    # Scenario 5: Plan found but violates constraints - provide plan details without constraint violations
                    logging.info(f"[{example_id}] Pass {pass_num} plan found but violates constraints, preparing constraint feedback")
                    plan_summary = f"Plan found: {pred_formatted}"
                    current_prompt = f"The previous solution produced the following plan:\n{plan_summary}\n\nHowever, this plan is incorrect and violates some constraints. Please revise your Z3 program to find a valid solution that satisfies all constraints.\n\nMake sure to surround your final code with ```python\nYOUR_CODE\n```."
            
            logging.warning(f"[{example_id}] FAILED to solve within {max_passes} passes")
            
            # Save final evaluation result even if we failed to solve
            if 'pred_formatted' in locals() and 'gold_formatted' in locals():
                # Determine the correct status based on what happened in the last pass
                if execution_output == "No code found in model response":
                    final_status = "No code extracted"
                elif execution_error:
                    final_status = f"Execution error: {execution_error}"
                elif no_plan_found:
                    final_status = f"No plan found: {pred_formatted.get('no_plan', 'Unknown reason')}"
                elif not constraints_satisfied:
                    final_status = "Wrong plan"
                else:
                    final_status = "Failed to solve within max passes"
                
                final_eval_result = {
                    "has_execution_error": bool(execution_error),
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
    """Main function to run the enhanced iterative SMT refinement"""
    args = parse_args()
    
    # Set up logging
    logging.info(f"Starting enhanced iterative SMT refinement")
    logging.info(f"Model: {args.model}")
    logging.info(f"Task: {args.task}")
    logging.info(f"Max passes: {args.max_passes}")
    logging.info(f"Max concurrent: {args.max_concurrent}")
    logging.info(f"Rate limit: {args.rate_limit} requests/minute")
    
    # Load data
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
    
    # Determine which examples to process
    if args.examples:
        # Process specific examples
        example_numbers = [int(x.strip()) for x in args.examples.split(',')]
        examples_to_process = []
        for num in example_numbers:
            example_id = f"{task_name_map[args.task]}_example_{num}"
            if example_id in data:
                examples_to_process.append((example_id, data[example_id]))
            else:
                logging.warning(f"Example {example_id} not found in data, skipping")
    elif args.start is not None or args.end is not None:
        # Filter examples by start/end range - same approach as parallel version
        logging.info(f"Filtering examples: start={args.start}, end={args.end}")
        # Convert examples dict to list of (example_id, example) tuples and slice
        examples_list = list(data.items())
        start_idx = args.start if args.start is not None else 0
        end_idx = args.end if args.end is not None else len(examples_list)
        
        # Slice the examples list
        filtered_examples_list = examples_list[start_idx:end_idx]
        examples_to_process = filtered_examples_list
        logging.info(f"Filtered to {len(examples_to_process)} examples (indices {start_idx} to {end_idx-1})")
    else:
        # Process all examples
        examples_to_process = list(data.items())
    
    logging.info(f"Processing {len(examples_to_process)} examples")
    
    # Clear output directories if fresh flag is set
    if args.fresh:
        output_base = f"../output/SMT/{args.model}/{args.task}/n_pass"
        if os.path.exists(output_base):
            shutil.rmtree(output_base)
            logging.info(f"Cleared output directory: {output_base}")
    
    # Set up rate limiting and concurrency
    rate_limiter = RateLimiter(args.rate_limit / 60.0)  # Convert to requests per second
    semaphore = asyncio.Semaphore(args.max_concurrent)
    
    # Process examples
    start_time = time.time()
    tasks = []
    
    for example_id, example in examples_to_process:
        constraints = constraints_data.get(example_id, {}).get("constraints", {})
        task = asyncio.create_task(
            process_single_example(
                example_id, example, constraints, args.model, 
                args.max_passes, rate_limiter, semaphore, args.task, args
            )
        )
        tasks.append(task)
    
    # Wait for all tasks to complete
    await asyncio.gather(*tasks, return_exceptions=True)
    
    total_time = time.time() - start_time
    logging.info(f"Completed processing {len(examples_to_process)} examples in {total_time:.2f} seconds")
    logging.info(f"Average time per example: {total_time / len(examples_to_process):.2f} seconds")

if __name__ == "__main__":
    asyncio.run(main()) 