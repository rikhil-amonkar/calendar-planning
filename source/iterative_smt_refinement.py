"""
Iterative SMT Refinement with Constraint Feedback

This script implements an iterative refinement process for solving scheduling problems using Z3 SMT solver.
It generates Z3 code using LLMs, executes it, evaluates constraints, and provides feedback for improvement.

Features:
1. Generates Z3 solution code using various LLM models (GPT, DeepSeek, etc.)
2. Executes the generated Python code and captures output
3. Evaluates the solution against domain-specific constraints using GPT-4.1-nano for answer extraction
4. Provides iterative feedback for constraint violations and execution errors
5. Saves conversation history, code, execution output, and evaluation results for each pass

Directory structure for outputs:
../output/SMT/{model_name}/{task}/n_pass/{example_id}/{pass_number}_pass/
  - conversation.json: Full conversation history
  - solution.py: Generated Z3 code
  - output.out: Execution output
  - evaluation.json: Constraint evaluation results

Usage:
python iterative_smt_refinement.py --task calendar --model gpt-4o-mini --start 0 --end 5
python iterative_smt_refinement.py --task all --model DeepSeek-V3 gpt-4o-mini --max_passes 3
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
import shutil
import logging

# Argument parsing
parser = argparse.ArgumentParser(
    description="Iterative SMT refinement with constraint feedback",
    formatter_class=argparse.RawDescriptionHelpFormatter,
    epilog="""
Examples:
  # Run calendar scheduling with GPT-4o-mini on examples 0-4
  python iterative_smt_refinement.py --task calendar --model gpt-4o-mini --start 0 --end 5
  
  # Run all tasks with multiple models, max 3 passes per example
  python iterative_smt_refinement.py --task all --model DeepSeek-V3 gpt-4o-mini --max_passes 3
  
  # Force re-run all examples (ignore existing results)
  python iterative_smt_refinement.py --task meeting --model o3-mini --fresh
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
parser.add_argument('--max_concurrent', type=int, default=10,
                   help="Maximum number of examples to process concurrently")
parser.add_argument('--rate_limit', type=float, default=1.0,
                   help="Requests per second limit (to avoid API rate limits)")
parser.add_argument('--examples', type=str, help="Comma-separated list of example numbers to rerun (e.g., '25,35')")
args = parser.parse_args()

try:
    with open("../../scheduling_key.json") as f:
        keys = json.load(f)
except FileNotFoundError:
    print("Error: scheduling_key.json not found. Please create this file with your API keys.")
    print("Expected format: {'openai': 'your_openai_key', 'deepseek': 'your_deepseek_key'}")
    exit(1)
except json.JSONDecodeError:
    print("Error: Invalid JSON in scheduling_key.json")
    exit(1)

def initialize_model(model_name, keys):
    """Initializes the Kani AI model based on the model name."""
    print(f"Running model: {model_name}")
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
        print(f"Output JSON: {output_json}")
        return json.loads(output_json)
    except Exception as e:
        print(f"Error in answer extraction: {e}")
        return {}

def evaluate_calendar(constraints, pred_dict):
    """Evaluate calendar constraints"""
    if not pred_dict or "day" not in pred_dict or "start_time" not in pred_dict or "end_time" not in pred_dict:
        return False, {"missing_fields": True}

    pred_day = pred_dict["day"]
    pred_start = pred_dict["start_time"]
    pred_end = pred_dict["end_time"]

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

    meeting_duration = constraints["meeting_duration"]
    if (pred_end - pred_start) != meeting_duration:
        return False, {"meeting_duration": meeting_duration}

    for disallowed_range in constraints["disallowed_ranges"]:
        if disallowed_range["day"] == pred_day:
            if (pred_start >= disallowed_range["start"] and pred_start < disallowed_range["end"]) or \
                    (pred_end > disallowed_range["start"] and pred_end <= disallowed_range["end"]) or \
                    (pred_start <= disallowed_range["start"] and pred_end >= disallowed_range["end"]):
                return False, disallowed_range
    return True, {}

def evaluate_trip(constraints, pred_dict):
    """Evaluate trip constraints"""
    segments = []
    for seg in pred_dict["itinerary"]:
        if not seg["day_range"].startswith("Day ") or "{" in seg["day_range"] or "}" in seg["day_range"]:
            return False, {"invalid_day_range_format": seg["day_range"]}

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

    total = constraints.get("trip_length")
    if not segments or segments[0]["start"] != 1 or segments[-1]["end"] != total:
        return False, {"total_days": total}

    for a, b in zip(segments, segments[1:]):
        if a["end"] != b["start"]:
            return False, {"gap/overlap": (a, b)}

    for seg in segments:
        required = constraints.get("stay_days", {}).get(seg["place"])
        if required is not None:
            actual = seg["end"] - seg["start"] + 1
            if actual != required:
                return False, {"stay_days": {seg["place"]: required}}

    for ev in constraints.get("city_day_ranges", []):
        place = ev["city"]
        container = next((s for s in segments if s["place"] == place), None)
        if not container:
            return False, {"missing_place": place}
        if container["start"] > ev["start"] or container["end"] < ev["end"]:
            return False, {"event_range": ev}

    allowed = [(d["from"], d["to"]) for d in constraints.get("direct_flights")]
    for a, b in zip(segments, segments[1:]):
        pair = (a["place"], b["place"])
        if pair not in allowed:
            return False, {"flight": {"from": a["place"], "to": b["place"]}}

    return True, {}

def evaluate_meeting(constraints, pred_dict):
    """Evaluate meeting constraints"""
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
    num_people_to_meet = constraints.get("num_people_to_meet", 0)

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

    if not meetings:
        return True, {}

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

def format_constraint_feedback(violated_constraints, task):
    """Format constraint violations into human-readable feedback"""
    if not violated_constraints:
        return ""

    feedback = "\nYour solution violates the following constraints:\n"

    if task == "calendar":
        if "meeting_duration" in violated_constraints:
            feedback += f"- The meeting duration must be exactly {violated_constraints['meeting_duration']} hours\n"
        if "day" in violated_constraints and "start" in violated_constraints:
            feedback += f"- The meeting time conflicts with an unavailable time slot on {violated_constraints['day']} from {violated_constraints['start']} to {violated_constraints['end']}\n"
    elif task == "trip":
        if "total_days" in violated_constraints:
            feedback += f"- The itinerary must cover exactly {violated_constraints['total_days']} days\n"
        if "stay_days" in violated_constraints:
            for place, required_days in violated_constraints["stay_days"].items():
                feedback += f"- Must stay in {place} for exactly {required_days} days\n"
        if "flight" in violated_constraints:
            flight = violated_constraints["flight"]
            feedback += f"- No direct flight available from {flight['from']} to {flight['to']}\n"
    elif task == "meeting":
        if "num_people_to_meet" in violated_constraints:
            feedback += f"- Must meet with exactly {violated_constraints['num_people_to_meet']} people\n"
        if "travel" in violated_constraints:
            travel = violated_constraints["travel"]
            feedback += f"- Not enough time to travel from {travel['from_location']} to {travel['to_location']} (need {travel['travel_time']} minutes)\n"
        if "person" in violated_constraints:
            feedback += f"- Meeting time with {violated_constraints['person']} is outside their availability\n"

    feedback += "\nPlease revise your solution to satisfy these constraints."
    return feedback

def execute_python_code(code_path):
    """Execute Python code and return output"""
    try:
        result = subprocess.run(
            ["python3", code_path],
            capture_output=True,
            text=True,
            timeout=10
        )
        return result.stdout + result.stderr
    except subprocess.TimeoutExpired:
        return "Error: Process timed out after 10 seconds."
    except Exception as e:
        return f"Error: {str(e)}"

async def run_model(ai, prompt):
    """Run the AI model with the given prompt"""
    response = await ai.chat_round_str(prompt)
    return response

task_name_map = {
    "calendar": "calendar_scheduling",
    "trip": "trip_planning",
    "meeting": "meeting_planning"
}

eval_functions = {
    "calendar": evaluate_calendar,
    "trip": evaluate_trip,
    "meeting": evaluate_meeting
}

def parse_args():
    """Parse command line arguments"""
    parser = argparse.ArgumentParser(description="Run iterative SMT refinement")
    parser.add_argument("--model", type=str, required=True, help="Model name to use")
    parser.add_argument("--task", type=str, choices=["calendar", "trip", "meeting"], required=True, help="Task to run")
    parser.add_argument("--max_passes", type=int, default=5, help="Maximum number of refinement passes")
    parser.add_argument("--rate_limit", type=float, default=1.0, help="API rate limit (requests per second)")
    parser.add_argument("--start", type=int, help="Start example number (inclusive)")
    parser.add_argument("--end", type=int, help="End example number (inclusive)")
    parser.add_argument("--fresh", action="store_true", help="Force fresh run even if output exists")
    parser.add_argument("--examples", type=str, help="Comma-separated list of example numbers to rerun (e.g., '25,35')")
    
    args = parser.parse_args()
    
    # Clean up examples argument
    if args.examples:
        # Remove all quotes and whitespace
        args.examples = args.examples.replace('"', '').replace("'", "").strip()
        # Split and clean each number
        args.examples = ','.join(num.strip() for num in args.examples.split(','))
    
    return args

def main():
    """Main execution function"""
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
    
    rate_limiter = RateLimiter(args.rate_limit)
    model_short_name = args.model.split("/")[-1] if "/" in args.model else args.model
    logging.info(f"Starting model: {args.model}")
    logging.info(f"Starting task: {args.task}")
    
    # Load examples and constraints
    examples = load_examples(args.task)
    constraints = load_constraints(args.task)
    
    # Handle specific examples if provided
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
                output_dir = f"../output/SMT/{model_short_name}/{args.task}/n_pass/{example_id}"
                if os.path.exists(output_dir):
                    logging.info(f"Clearing output directory for {example_id}")
                    shutil.rmtree(output_dir)
        except ValueError as e:
            logging.error(f"Error parsing example numbers: {e}")
            logging.error(f"Raw examples string: '{args.examples}'")
            return
    
    # Process examples
    success_count = 0
    failed_count = 0
    error_count = 0
    
    for example_id, example in examples.items():
        # Verify example_id matches task prefix
        task_prefix = task_prefix_map[args.task]
        if not example_id.startswith(f"{task_prefix}_example_"):
            logging.warning(f"Example ID {example_id} does not match expected format for task {args.task}, skipping")
            continue
            
        if example_id not in constraints:
            logging.warning(f"No constraints found for {example_id}, skipping")
            continue
            
        # Skip examples outside the range if specified
        if args.start is not None or args.end is not None:
            example_num = int(example_id.split("_")[-1])
            if (args.start is not None and example_num < args.start) or \
               (args.end is not None and example_num >= args.end):
                continue
        
        try:
            result = process_single_example(
                args.model,
                model_short_name,
                args.task,
                example_id,
                example,
                constraints[example_id],
                rate_limiter
            )
            
            if result["status"] == "success":
                success_count += 1
            elif result["status"] == "failed":
                failed_count += 1
            elif result["status"] == "api_error":
                error_count += 1
                
        except Exception as e:
            logging.error(f"Error processing {example_id}: {str(e)}")
            error_count += 1
    
    logging.info(f"Results: {success_count} succeeded, {failed_count} failed, {error_count} API errors")

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
    main()