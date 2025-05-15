import os
import json
import argparse

# Argument parsing
parser = argparse.ArgumentParser(description="")
parser.add_argument('--task', choices=['calendar', 'trip', 'meeting', 'all'], required=True, help="")
parser.add_argument('--model', required=True, help="")
args = parser.parse_args()

directory = f'../output/SMT/{args.model}/{args.task}/formatted_output'

has_error_false = 0
final_program_time_not_empty = 0
is_correct_true = 0

for filename in os.listdir(directory):
    if filename.endswith('.json'):
        filepath = os.path.join(directory, filename)
        with open(filepath, 'r', encoding='utf-8') as f:
            data = json.load(f)
            # Assuming the structure is as shown in your example
            entry = data.get("0shot", [{}])[0]
            if entry.get("has_error") is False:
                has_error_false += 1
            if entry.get("final_program_time") and "itinerary" not in entry.get("final_program_time") or "itinerary" in entry.get("final_program_time") and entry.get("final_program_time").get("itinerary"):
                final_program_time_not_empty += 1
            if entry.get("is_correct") is True:
                is_correct_true += 1

print(f'"has_error": false count: {has_error_false}')
print(f'"final_program_time" not empty count: {final_program_time_not_empty}')
print(f'"is_correct": true count: {is_correct_true}')