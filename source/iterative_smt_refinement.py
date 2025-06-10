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
                   help="Task to run: calendar (scheduling meetings), trip (planning itineraries), meeting (scheduling multiple meetings), or all")
parser.add_argument('--model', required=True, nargs='+', 
                   help="Model(s) to use: gpt-4o-mini, o3-mini, DeepSeek-V3, DeepSeek-R1, or any HuggingFace model path")
parser.add_argument('--fresh', action='store_true', 
                   help="Re-run all examples, ignoring existing successful solutions")
parser.add_argument('--start', type=int, default=0, 
                   help="Starting index for processing examples (default: 0)")
parser.add_argument('--end', type=int, default=-1, 
                   help="Ending index for processing examples (default: -1, process all)")
parser.add_argument('--max_passes', type=int, default=5, 
                   help="Maximum number of refinement passes per example (default: 5)")
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

async def main():
    """Main execution function"""
    for model_name in args.model:
        ai = initialize_model(model_name, keys)
        model_short_name = model_name.split("/")[-1] if "/" in model_name else model_name

        if args.task == "all":
            tasks = ["calendar", "trip", "meeting"]
        else:
            tasks = [args.task]

        for task in tasks:
            print(f"Running task: {task}")
            
            # Load data and constraints
            with open(f"../data/{task_name_map[task]}_100.json") as f:
                data = json.load(f)
            
            with open(f"../data/{task_name_map[task]}_100_constraints.json") as f:
                constraints_data = json.load(f)

            for idx, (example_id, example) in enumerate(data.items()):
                if idx < args.start or (args.end != -1 and idx >= args.end):
                    continue
                
                print(f"Processing example: {example_id}")
                
                # Check if we should skip this example
                base_output_dir = f"../output/SMT/{model_short_name}/{task}/n_pass/{example_id}"
                if not args.fresh and os.path.exists(base_output_dir):
                    # Check if we already have a successful solution
                    for pass_num in range(1, args.max_passes + 1):
                        eval_path = f"{base_output_dir}/{pass_num}_pass/evaluation.json"
                        if os.path.exists(eval_path):
                            with open(eval_path, 'r') as f:
                                eval_data = json.load(f)
                                if eval_data.get("constraints_satisfied", False):
                                    print(f"Skipping {example_id}, already has successful solution in pass {pass_num}")
                                    break
                    else:
                        # No successful solution found, continue processing
                        pass
                    continue

                # Get constraints for this example
                example_constraints = constraints_data.get(example_id, {}).get("constraints", {})
                
                # Initialize conversation history
                conversation_history = []
                
                # Initial prompt
                initial_prompt = "Given the following scheduling problem:\n"
                initial_prompt += f"{example['prompt_0shot']}\n"
                if task == "calendar":
                    initial_prompt += "Your solution should always have three things: the day to meet, the start time, and the end time.\n"
                if task == "trip":
                    initial_prompt += "Note that if one flies from city A to city B on day X, then they are in both cities A and B on day X, which contributes to the total number of days in each city.\n"
                initial_prompt += "Write a Python program that solves it using the Z3 solver. Always surround your final code with ```python\nYOUR_CODE\n```.\n"
                
                current_prompt = initial_prompt
                
                for pass_num in range(1, args.max_passes + 1):
                    print(f"Pass {pass_num} for example {example_id}")
                    
                    # Create output directory for this pass
                    pass_output_dir = f"{base_output_dir}/{pass_num}_pass"
                    os.makedirs(pass_output_dir, exist_ok=True)
                    
                    # Get response from model
                    while True:
                        try:
                            response_txt = await run_model(ai, current_prompt)
                            break
                        except Exception as e:
                            print(f"An error occurred: {e}. Retrying in 5 seconds...")
                            time.sleep(5)
                            ai = initialize_model(model_name, keys)
                    
                    # Add to conversation history
                    conversation_history.append({
                        "role": "user",
                        "content": current_prompt
                    })
                    conversation_history.append({
                        "role": "assistant", 
                        "content": response_txt
                    })
                    
                    # Save conversation
                    with open(f"{pass_output_dir}/conversation.json", "w") as f:
                        json.dump(conversation_history, f, indent=4)
                    
                    # Extract and save code
                    generated_code = extract_code(response_txt)
                    code_path = f"{pass_output_dir}/solution.py"
                    with open(code_path, "w") as f:
                        f.write(generated_code)
                    
                    # Execute code
                    execution_output = execute_python_code(code_path)
                    with open(f"{pass_output_dir}/output.out", "w") as f:
                        f.write(execution_output)
                    
                    # Check if execution had errors
                    has_execution_error = ("Error" in execution_output or 
                                         "Exception" in execution_output or 
                                         "Traceback" in execution_output or
                                         not execution_output.strip())
                    
                    if has_execution_error:
                        # Extract gold plan for consistency
                        gold = example["golden_plan"]
                        if isinstance(gold, list):
                            gold = "\n".join(gold)
                        try:
                            gold_formatted = extract_answer(gold, task)
                        except Exception as e:
                            gold_formatted = {}
                        
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
                        
                        continue
                    
                    # Extract structured answer from execution output
                    try:
                        pred_formatted = extract_answer(execution_output, task)
                    except Exception as e:
                        pred_formatted = {}
                    
                    # Extract gold plan
                    gold = example["golden_plan"]
                    if isinstance(gold, list):
                        gold = "\n".join(gold)
                    try:
                        gold_formatted = extract_answer(gold, task)
                    except Exception as e:
                        gold_formatted = {}
                    
                    # Evaluate constraints
                    eval_func = eval_functions[task]
                    
                    # Special handling for meeting task
                    if task == "meeting":
                        # Add num_people_to_meet constraint from gold solution
                        num_people_to_meet = len(gold_formatted.get("itinerary", []))
                        example_constraints["num_people_to_meet"] = num_people_to_meet
                    
                    constraints_satisfied, violated_constraints = eval_func(example_constraints, pred_formatted)
                    
                    # Check exact match
                    is_exact_match = pred_formatted == gold_formatted
                    
                    # Determine status
                    if constraints_satisfied:
                        status = "Correct"
                    else:
                        status = "Wrong plan"
                    
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
                        print(f"Success! Example {example_id} solved in pass {pass_num}")
                        break
                    else:
                        # Prepare feedback for next iteration
                        constraint_feedback = format_constraint_feedback(violated_constraints, task)
                        current_prompt = f"The previous solution produced the following output:\n{execution_output}\n{constraint_feedback}\n\nPlease revise your solution to satisfy these constraints. Make sure to surround your final code with ```python\nYOUR_CODE\n```."
                
                else:
                    print(f"Failed to solve example {example_id} within {args.max_passes} passes")

if __name__ == "__main__":
    asyncio.run(main()) 