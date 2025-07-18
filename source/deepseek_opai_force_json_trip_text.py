#**********WORKING CODE, FORCE JSON, TEXT OUTPUTS, TRIP PLANNING, DEEPSEEK (WITH STATE MANAGEMENT)************

import argparse
import json
import datetime
import re
import os
from openai import OpenAI

# Read the API key from a file
with open('/home/rma336/openai_research/deepseek_api_key.txt', 'r') as key_file:
    api_key = key_file.read().strip()

# Initialize the OpenAI client for DeepSeek
client = OpenAI(
    api_key=api_key,
    base_url="https://api.deepseek.com"
)

# Define the structured JSON schema for the trip plan output
JSON_SCHEMA = {
    "name": "trip_plan_schema",
    "schema": {
        "type": "object",
        "properties": {
            "itinerary": {
                "type": "array",
                "items": {
                    "anyOf": [
                        {
                            "type": "object",
                            "properties": {
                                "day_range": {"type": "string", "pattern": "^Day \\d+-\\d+$"},
                                "place": {"type": "string"}
                            },
                            "required": ["day_range", "place"]
                        },
                        {
                            "type": "object",
                            "properties": {
                                "flying": {"type": "string", "pattern": "^Day \\d+-\\d+$"},
                                "from": {"type": "string"},
                                "to": {"type": "string"}
                            },
                            "required": ["flying", "from", "to"]
                        }
                    ]
                }
            }
        },
        "required": ["itinerary"]
    }
}

# Load the trip planning examples from the JSON file
with open('../../data/trip_planning_100.json', 'r') as file:
    trip_examples = json.load(file)

# Argument parser to select the model
parser = argparse.ArgumentParser(description="Select an OpenAI model.")
parser.add_argument('--model', type=str, required=True, help="The OpenAI model ID to use.")
args = parser.parse_args()

# State management
STATE_FILE = "deepseek_trip_planning_state.json"

class EvaluationState:
    def __init__(self):
        self.correct_0shot = 0
        self.total_0shot = 0
        self.results_0shot = []
        self.processed_examples = set()
        self.start_time = datetime.datetime.now()
        self.previous_time = datetime.timedelta(0)
        self.first_run = True

    def save(self):
        state_to_save = {
            "correct_0shot": self.correct_0shot,
            "total_0shot": self.total_0shot,
            "results_0shot": self.results_0shot,
            "processed_examples": list(self.processed_examples),
            "start_time": self.start_time.isoformat(),
            "previous_time": self.previous_time.total_seconds(),
            "first_run": self.first_run
        }
        with open(STATE_FILE, 'w') as f:
            json.dump(state_to_save, f)

    def load(self):
        try:
            with open(STATE_FILE, 'r') as f:
                loaded = json.load(f)
                self.correct_0shot = loaded["correct_0shot"]
                self.total_0shot = loaded["total_0shot"]
                self.results_0shot = loaded["results_0shot"]
                self.processed_examples = set(loaded["processed_examples"])
                self.previous_time = datetime.timedelta(seconds=loaded["previous_time"])
                self.start_time = datetime.datetime.fromisoformat(loaded["start_time"])
                self.first_run = loaded.get("first_run", False)
            return True
        except (FileNotFoundError, json.JSONDecodeError, KeyError):
            return False

def parse_golden_plan(golden_plan):
    """Parse the golden plan into structured itinerary format matching our JSON schema."""
    itinerary = []
    
    # Split the plan into lines and process each line
    for line in golden_plan.split('\n'):
        line = line.strip()
        if not line or not line.startswith('**Day'):
            continue
            
        # Extract day range
        day_match = re.search(r'Day (\d+)(?:-(\d+))?', line)
        if not day_match:
            continue
            
        start_day = int(day_match.group(1))
        end_day = int(day_match.group(2)) if day_match.group(2) else start_day
        day_range = f"Day {start_day}-{end_day}"
        
        # Handle flying days
        if "Fly from" in line:
            fly_match = re.search(r'Fly from ([^\s,.]+) to ([^\s,.]+)', line)
            if fly_match:
                itinerary.append({
                    "flying": day_range,
                    "from": fly_match.group(1),
                    "to": fly_match.group(2)
                })
            continue
        # Handle regular days
        elif "Arriving in" in line:
            place = re.search(r'Arriving in ([^\s,.]+)', line).group(1)
        elif "Visit" in line:
            place = re.search(r'Visit ([^\s,.]+)', line).group(1)
        else:
            continue  # skip if we couldn't determine the type
            
        # Add to itinerary
        itinerary.append({
            "day_range": day_range,
            "place": place
        })
    
    return itinerary

def compare_itineraries(model_itinerary, golden_itinerary):
    """Compare two itineraries and return True if they match exactly."""
    if len(model_itinerary) != len(golden_itinerary):
        return False
    
    for model_item, golden_item in zip(model_itinerary, golden_itinerary):
        # Check if both items are the same type
        if ("day_range" in model_item) != ("day_range" in golden_item):
            return False
        if ("flying" in model_item) != ("flying" in golden_item):
            return False
        
        # Compare based on type
        if "day_range" in model_item:
            if (model_item["day_range"] != golden_item["day_range"] or 
                model_item["place"] != golden_item["place"]):
                return False
        elif "flying" in model_item:
            if (model_item["flying"] != golden_item["flying"] or 
                model_item["from"] != golden_item["from"] or 
                model_item["to"] != golden_item["to"]):
                return False
    
    return True

def format_itinerary_compact(itinerary):
    """Convert itinerary to compact string representation for display."""
    parts = []
    for item in itinerary:
        if "day_range" in item:
            parts.append(f"{item['day_range']}: {item['place']}")
        elif "flying" in item:
            parts.append(f"{item['flying']}: {item['from']}→{item['to']}")
    return ", ".join(parts)

def main():
    # Initialize state
    state = EvaluationState()
    state_loaded = state.load()

    # Determine file open mode
    txt_mode = 'a' if state_loaded and not state.first_run else 'w'
    json_mode = 'a' if state_loaded and not state.first_run else 'w'

    with open('DS-R1-FULL_forceJSON_text_trip_results.txt', txt_mode) as txt_file, \
         open('DS-R1-FULL_forceJSON_text_trip_results.json', json_mode) as json_file:
        
        # Write header if this is a fresh run
        if not state_loaded or state.first_run:
            txt_file.write("=== New Run Started ===\n")
            json_file.write("")  # Will be properly initialized later
            state.first_run = False

        for example_id, example in trip_examples.items():
            # Skip already processed examples
            if example_id in state.processed_examples:
                continue
                
            for prompt_type in ['prompt_0shot']:
                prompt = example[prompt_type]
                golden_plan = example['golden_plan']

                # Parse golden plan into structured format
                golden_itinerary = parse_golden_plan(golden_plan)

                # Modify prompt to request structured JSON output
                structured_prompt = (
                    "You are a AI trip planner and your task is to plan a trip for a user. "
                    "Days that involve flying happen on the same day. Include them in the plan with the flying details. "
                    "Ensure clear, structured, and diverse responses. avoiding unnecessary repetition. "
                    f"{prompt}\n\nPlease provide your trip plan in the following exact JSON format:\n"
                    "{\n"
                    '  "itinerary": [\n'
                    '    {"day_range": "Day X-Y", "place": "City Name"},\n'
                    '    {"flying": "Day Y-Y", "from": "City Name", "to": "City Name"},\n'
                    '    {"day_range": "Day Y-Z", "place": "City Name"}\n'
                    "  ]\n"
                    "}"
                )

                # Run the model with DeepSeek API
                response = client.chat.completions.create(
                    model="deepseek-chat",
                    messages=[
                        {"role": "system", "content": "You are a helpful assistant that plans trips in JSON format."},
                        {"role": "user", "content": structured_prompt}
                    ]
                )

                model_response = response.choices[0].message.content

                try:
                    # Try to parse the response as JSON
                    model_data = json.loads(model_response)
                    model_itinerary = model_data.get("itinerary", [])
                except json.JSONDecodeError:
                    # If parsing fails, try to extract JSON from the response
                    try:
                        json_match = re.search(r'```json\n(.*?)\n```', model_response, re.DOTALL)
                        if json_match:
                            model_data = json.loads(json_match.group(1))
                            model_itinerary = model_data.get("itinerary", [])
                        else:
                            model_itinerary = []
                    except:
                        model_itinerary = []

                # Compare with golden itinerary
                is_correct = compare_itineraries(model_itinerary, golden_itinerary)

                # Update counters
                if prompt_type == 'prompt_0shot':
                    state.total_0shot += 1
                    if is_correct:
                        state.correct_0shot += 1

                # Prepare result entry
                result_entry = {
                    "example_id": example_id,
                    "prompt_type": prompt_type,
                    "model_response": model_response,
                    "model_itinerary": model_itinerary,
                    "golden_itinerary": golden_itinerary,
                    "is_correct": is_correct
                }

                # Store results
                if prompt_type == 'prompt_0shot':
                    state.results_0shot.append(result_entry)

                # Format for display
                model_display = format_itinerary_compact(model_itinerary)
                golden_display = format_itinerary_compact(golden_itinerary)
                
                # Log output
                timestamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                output_line = (
                    f"{example_id}. [{timestamp}] | {prompt_type} | Correct: {is_correct} | ANSWER: {model_display} | EXPECTED: {golden_display}"
                )
                print(output_line)
                txt_file.write(f"{output_line}\n")

                # Save state after each example
                state.processed_examples.add(example_id)
                state.save()

        # Final results handling
        current_time = datetime.datetime.now()
        total_runtime = state.previous_time + (current_time - state.start_time)
        
        # Write the collected results to the JSON file in the desired format
        json.dump({
            "0shot": state.results_0shot,
            "accuracy": {
                "0shot": state.correct_0shot / state.total_0shot if state.total_0shot > 0 else 0
            }
        }, json_file, indent=4)

        # Calculate accuracy
        accuracy_0shot = (state.correct_0shot / state.total_0shot) * 100 if state.total_0shot > 0 else 0
        
        # Write the final accuracy to the text file
        txt_file.write("\n=== Final Results ===\n")
        txt_file.write(f"0-shot prompts: Model guessed {state.correct_0shot} out of {state.total_0shot} correctly.\n")
        txt_file.write(f"Accuracy: {accuracy_0shot:.2f}%\n")
        txt_file.write(f"Total time taken: {total_runtime}\n")

    print("Processing complete. Results saved.")

if __name__ == "__main__":
    main()




# # #**********WORKING CODE, FORCE JSON, TEXT OUTPUTS, TRIP PLANNING, DEEPSEEK************

# import argparse
# import json
# import datetime
# import re
# from openai import OpenAI

# # Read the API key from a file
# with open('/home/rma336/openai_research/deepseek_api_key.txt', 'r') as key_file:
#     api_key = key_file.read().strip()

# # Initialize the OpenAI client for DeepSeek
# client = OpenAI(
#     api_key=api_key,
#     base_url="https://api.deepseek.com"
# )

# # Define the structured JSON schema for the trip plan output
# JSON_SCHEMA = {
#     "name": "trip_plan_schema",
#     "schema": {
#         "type": "object",
#         "properties": {
#             "itinerary": {
#                 "type": "array",
#                 "items": {
#                     "anyOf": [
#                         {
#                             "type": "object",
#                             "properties": {
#                                 "day_range": {"type": "string", "pattern": "^Day \\d+-\\d+$"},
#                                 "place": {"type": "string"}
#                             },
#                             "required": ["day_range", "place"]
#                         },
#                         {
#                             "type": "object",
#                             "properties": {
#                                 "flying": {"type": "string", "pattern": "^Day \\d+-\\d+$"},
#                                 "from": {"type": "string"},
#                                 "to": {"type": "string"}
#                             },
#                             "required": ["flying", "from", "to"]
#                         }
#                     ]
#                 }
#             }
#         },
#         "required": ["itinerary"]
#     }
# }

# # Load the trip planning examples from the JSON file
# with open('../../data/trip_planning_100.json', 'r') as file:
#     trip_examples = json.load(file)

# # Argument parser to select the model
# parser = argparse.ArgumentParser(description="Select an OpenAI model.")
# parser.add_argument('--model', type=str, required=True, help="The OpenAI model ID to use.")
# args = parser.parse_args()

# def parse_golden_plan(golden_plan):
#     """Parse the golden plan into structured itinerary format matching our JSON schema."""
#     itinerary = []
    
#     # Split the plan into lines and process each line
#     for line in golden_plan.split('\n'):
#         line = line.strip()
#         if not line or not line.startswith('**Day'):
#             continue
            
#         # Extract day range
#         day_match = re.search(r'Day (\d+)(?:-(\d+))?', line)
#         if not day_match:
#             continue
            
#         start_day = int(day_match.group(1))
#         end_day = int(day_match.group(2)) if day_match.group(2) else start_day
#         day_range = f"Day {start_day}-{end_day}"
        
#         # Handle flying days
#         if "Fly from" in line:
#             fly_match = re.search(r'Fly from ([^\s,.]+) to ([^\s,.]+)', line)
#             if fly_match:
#                 itinerary.append({
#                     "flying": day_range,
#                     "from": fly_match.group(1),
#                     "to": fly_match.group(2)
#                 })
#             continue
#         # Handle regular days
#         elif "Arriving in" in line:
#             place = re.search(r'Arriving in ([^\s,.]+)', line).group(1)
#         elif "Visit" in line:
#             place = re.search(r'Visit ([^\s,.]+)', line).group(1)
#         else:
#             continue  # skip if we couldn't determine the type
            
#         # Add to itinerary
#         itinerary.append({
#             "day_range": day_range,
#             "place": place
#         })
    
#     return itinerary

# def compare_itineraries(model_itinerary, golden_itinerary):
#     """Compare two itineraries and return True if they match exactly."""
#     if len(model_itinerary) != len(golden_itinerary):
#         return False
    
#     for model_item, golden_item in zip(model_itinerary, golden_itinerary):
#         # Check if both items are the same type
#         if ("day_range" in model_item) != ("day_range" in golden_item):
#             return False
#         if ("flying" in model_item) != ("flying" in golden_item):
#             return False
        
#         # Compare based on type
#         if "day_range" in model_item:
#             if (model_item["day_range"] != golden_item["day_range"] or 
#                 model_item["place"] != golden_item["place"]):
#                 return False
#         elif "flying" in model_item:
#             if (model_item["flying"] != golden_item["flying"] or 
#                 model_item["from"] != golden_item["from"] or 
#                 model_item["to"] != golden_item["to"]):
#                 return False
    
#     return True

# def format_itinerary_compact(itinerary):
#     """Convert itinerary to compact string representation for display."""
#     parts = []
#     for item in itinerary:
#         if "day_range" in item:
#             parts.append(f"{item['day_range']}: {item['place']}")
#         elif "flying" in item:
#             parts.append(f"{item['flying']}: {item['from']}→{item['to']}")
#     return ", ".join(parts)

# # Initialize counters
# correct_0shot = 0
# # correct_5shot = 0
# total_0shot = 0
# # total_5shot = 0

# # Initialize results lists
# results_0shot = []
# # results_5shot = []

# # Output files
# with open('DS-R1-FULL_forceJSON_text_trip_results.txt', 'w') as txt_file, open('DS-R1-FULL_forceJSON_text_trip_results.json', 'w') as json_file:
#     start_time = datetime.datetime.now()
    
#     for example_id, example in trip_examples.items():
#         for prompt_type in ['prompt_0shot']:
#             prompt = example[prompt_type]
#             golden_plan = example['golden_plan']

#             # Parse golden plan into structured format
#             golden_itinerary = parse_golden_plan(golden_plan)

#             # Modify prompt to request structured JSON output
#             structured_prompt = (
#                 "You are a AI trip planner and your task is to plan a trip for a user. "
#                 "Days that involve flying happen on the same day. Include them in the plan with the flying details. "
#                 "Ensure clear, structured, and diverse responses. avoiding unnecessary repetition. "
#                 f"{prompt}\n\nPlease provide your trip plan in the following exact JSON format:\n"
#                 "{\n"
#                 '  "itinerary": [\n'
#                 '    {"day_range": "Day X-Y", "place": "City Name"},\n'
#                 '    {"flying": "Day Y-Y", "from": "City Name", "to": "City Name"},\n'
#                 '    {"day_range": "Day Y-Z", "place": "City Name"}\n'
#                 "  ]\n"
#                 "}"
#             )

#             # Run the model with DeepSeek API
#             response = client.chat.completions.create(
#                 model="deepseek-chat",  # Using DeepSeek model
#                 messages=[
#                     {"role": "system", "content": "You are a helpful assistant that plans trips in JSON format."},
#                     {"role": "user", "content": structured_prompt}
#                 ],
#                 # Note: DeepSeek API might not support response_format parameter
#                 # response_format={
#                 #     "type": "json_schema",
#                 #     "json_schema": JSON_SCHEMA
#                 # }
#             )

#             model_response = response.choices[0].message.content

#             try:
#                 # Try to parse the response as JSON
#                 model_data = json.loads(model_response)
#                 model_itinerary = model_data.get("itinerary", [])
#             except json.JSONDecodeError:
#                 # If parsing fails, try to extract JSON from the response
#                 try:
#                     json_match = re.search(r'```json\n(.*?)\n```', model_response, re.DOTALL)
#                     if json_match:
#                         model_data = json.loads(json_match.group(1))
#                         model_itinerary = model_data.get("itinerary", [])
#                     else:
#                         model_itinerary = []
#                 except:
#                     model_itinerary = []

#             # Compare with golden itinerary
#             is_correct = compare_itineraries(model_itinerary, golden_itinerary)

#             # Update counters
#             if prompt_type == 'prompt_0shot':
#                 total_0shot += 1
#                 if is_correct:
#                     correct_0shot += 1
#             # else:
#             #     total_5shot += 1
#             #     if is_correct:
#             #         correct_5shot += 1

#             # Prepare result entry
#             result_entry = {
#                 "example_id": example_id,
#                 "prompt_type": prompt_type,
#                 "model_response": model_response,
#                 "model_itinerary": model_itinerary,
#                 "golden_itinerary": golden_itinerary,
#                 "is_correct": is_correct
#             }

#             # Store results
#             if prompt_type == 'prompt_0shot':
#                 results_0shot.append(result_entry)
#             # else:
#             #     results_5shot.append(result_entry)

#             # Format for display
#             model_display = format_itinerary_compact(model_itinerary)
#             golden_display = format_itinerary_compact(golden_itinerary)
            
#             # Log output
#             timestamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
#             output_line = (
#                 f"{example_id}. [{timestamp}] | {prompt_type} | Correct: {is_correct} | ANSWER: {model_display} | EXPECTED: {golden_display}"
#             )
#             print(output_line)
#             txt_file.write(f"{output_line}\n")

#     # Save JSON results
#     json.dump({
#         "0shot": results_0shot,
#         # "5shot": results_5shot,
#         "accuracy": {
#             "0shot": correct_0shot / total_0shot if total_0shot > 0 else 0
#             # "5shot": correct_5shot / total_5shot if total_5shot > 0 else 0,
#             # "total": (correct_0shot + correct_5shot) / (total_0shot + total_5shot) if (total_0shot + total_5shot) > 0 else 0
#         }
#     }, json_file, indent=4)

#     # Final accuracy report
#     end_time = datetime.datetime.now()
#     total_time = end_time - start_time
#     txt_file.write("\n=== Final Results ===\n")
#     txt_file.write(f"0-shot accuracy: {correct_0shot}/{total_0shot} ({correct_0shot/total_0shot:.2%})\n")
#     # txt_file.write(f"5-shot accuracy: {correct_5shot}/{total_5shot} ({correct_5shot/total_5shot:.2%})\n")
#     # txt_file.write(f"Total accuracy: {correct_0shot + correct_5shot}/{total_0shot + total_5shot} ({(correct_0shot + correct_5shot)/(total_0shot + total_5shot):.2%})\n")
#     txt_file.write(f"Total time: {total_time}\n")

# print("Processing complete. Results saved to openai_forceJSON_text_trip_results.txt and openai_forceJSON_text_trip_results.json.")