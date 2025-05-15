import argparse
from openai import OpenAI
import json
import os

with open("../../scheduling_key.json") as f:
    key = json.load(f)["openai"]
client = OpenAI(api_key=key)

# Argument parsing
parser = argparse.ArgumentParser(description="")
parser.add_argument('--task', choices=['calendar', 'trip', 'meeting', 'all'], required=True, help="")
parser.add_argument('--model', required=True, help="")
args = parser.parse_args()

def evaluate_calendar(constraints, pred_dict):
    pred_day = pred_dict["day"]
    pred_start = pred_dict["start_time"]
    pred_end = pred_dict["end_time"]
    # Convert time strings to numerical values
    if isinstance(pred_start, str):
        pred_start_parts = pred_start.split(":")
        pred_start = float(pred_start_parts[0]) + float(pred_start_parts[1]) / 60

    if isinstance(pred_end, str):
        pred_end_parts = pred_end.split(":")
        pred_end = float(pred_end_parts[0]) + float(pred_end_parts[1]) / 60
    for disallowed_range in constraints["disallowed_ranges"]:
        if disallowed_range["day"] == pred_day:
            if (pred_start >= disallowed_range["start"] and pred_start < disallowed_range["end"]) or \
               (pred_end > disallowed_range["start"] and pred_end <= disallowed_range["end"]) or \
               (pred_start <= disallowed_range["start"] and pred_end >= disallowed_range["end"]):
                print(pred_dict)
                print(f"Constraint violated: {pred_day} {pred_start} - {pred_end} overlaps with {disallowed_range['start']} - {disallowed_range['end']}")
                #raise SystemExit
                return False
    return True

def evaluate_trip(constraints, pred_dict):
    pred_itinerary = pred_dict["itinerary"]
    pass

task_name_map = {
    "calendar": "calendar_scheduling",
    "trip": "trip_planning",
    "meeting": "meeting_planning"
}

task_function_map = {
    "calendar": evaluate_calendar,
    "trip": evaluate_trip,
    "meeting": None  # Placeholder for meeting evaluation function
}

if args.task == "all":
    tasks = ["calendar", "trip", "meeting"]
else:
    tasks = [args.task]

model = args.model
for task in tasks:
    # Load constraints
    with open(f"../data/{task_name_map[task]}_100_constraints.json") as f:
        constraints_data = json.load(f)
        
    # Initialize evaluation results
    results = {
        "total": 0,
        "constraint_satisfied": 0
    }
    
    # Get the evaluation function for this task
    eval_func = task_function_map[task]
    if eval_func is None:
        print(f"Skipping {task} as evaluation function is not implemented")
        continue
        
    # Directory with formatted outputs
    output_dir = f"../output/SMT/{model}/{task}/formatted_output"
    
    # Process each file
    for filename in os.listdir(output_dir):
        if not filename.endswith('.json'):
            continue
            
        with open(os.path.join(output_dir, filename), 'r') as f:
            output_data = json.load(f)
            
        example_id = filename.replace('.json', '')
        print(f"Processing example {example_id}")
        
        # Extract prediction from the formatted output
        entry = output_data.get("0shot", [{}])[0]
        pred_dict = entry.get("final_program_time")
        
        # Skip examples without predictions
        if not pred_dict:
            continue
            
        # Get constraints for this example
        example_constraints = constraints_data.get(example_id, {}).get("constraints", {})
        
        # Evaluate if prediction satisfies constraints
        results["total"] += 1
        if eval_func(example_constraints, pred_dict):
            results["constraint_satisfied"] += 1
    
    # Calculate and print results
    if results["total"] > 0:
        satisfaction_rate = results["constraint_satisfied"] / results["total"] * 100
        print(f"Model: {model}, Task: {task_name_map[task]}")
        print(f"  Constraint satisfaction rate: {satisfaction_rate:.2f}% ({results['constraint_satisfied']}/{results['total']})")
    else:
        print(f"No valid examples found for Model: {model}, Task: {task_name_map[task]}")
