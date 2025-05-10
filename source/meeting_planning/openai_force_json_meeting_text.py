# #**********WORKING CODE, FORCE JSON, TEXT OUTPUTS, MEETING PLANNING, OPENAI, CHECKPOINT************

import argparse
import asyncio
import json
import datetime
import re
from openai import OpenAI

# Read the API key from a file
with open('/home/rma336/openai_research/openai_api_key.txt', 'r') as key_file:
    api_key = key_file.read().strip()

# Initialize the OpenAI client
client = OpenAI(api_key=api_key)

# Define the structured JSON schema for the meeting plan output
JSON_SCHEMA = {
    "name": "meeting_plan_schema",
    "schema": {
        "type": "object",
        "properties": {
            "itinerary": {
                "type": "array",
                "items": {
                    "type": "object",
                    "properties": {
                        "action": {"type": "string", "enum": ["meet"]},
                        "location": {"type": "string"},
                        "person": {"type": "string"},
                        "start_time": {"type": "string"},
                        "end_time": {"type": "string"}
                    },
                    "required": ["action", "location", "person", "start_time", "end_time"]
                }
            }
        },
        "required": ["itinerary"]
    }
}

# Load the meeting planning examples from the JSON file
with open('../../data/meeting_planning_100.json', 'r') as file:
    meeting_examples = json.load(file)

# Argument parser to select the model
parser = argparse.ArgumentParser(description="Select an OpenAI model.")
parser.add_argument('--model', type=str, required=True, help="The OpenAI model ID to use.")
args = parser.parse_args()

# State management
STATE_FILE = "meeting_planning_state_openai.json"

class EvaluationState:
    def __init__(self):
        self.results_0shot = []
        self.processed_examples = set()
        self.start_time = datetime.datetime.now()
        self.previous_time = datetime.timedelta(0)
        self.first_run = True

    def save(self):
        state_to_save = {
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
                self.results_0shot = loaded["results_0shot"]
                self.processed_examples = set(loaded["processed_examples"])
                self.previous_time = datetime.timedelta(seconds=loaded["previous_time"])
                self.start_time = datetime.datetime.fromisoformat(loaded["start_time"])
                self.first_run = loaded.get("first_run", False)
            return True
        except (FileNotFoundError, json.JSONDecodeError, KeyError):
            return False

def convert_to_24hour(time_str):
    """Convert time string to 24-hour format without leading zeros."""
    # Remove any spaces and make uppercase
    time_str = time_str.replace(" ", "").upper()
    
    # Handle case where time might already be in 24-hour format
    if 'AM' not in time_str and 'PM' not in time_str:
        # Try to parse as 24-hour format
        try:
            hours, minutes = map(int, time_str.split(':'))
            if hours < 0 or hours > 23 or minutes < 0 or minutes > 59:
                return None
            return f"{hours}:{minutes:02d}"
        except:
            return None
    
    # Split into time and period
    time_part = time_str[:-2]
    period = time_str[-2:]
    
    # Split hours and minutes
    try:
        if ':' in time_part:
            hours, minutes = map(int, time_part.split(':'))
        else:
            hours = int(time_part)
            minutes = 0
    except:
        return None
    
    # Validate time
    if hours < 0 or hours > 12 or minutes < 0 or minutes > 59:
        return None
    
    # Convert to 24-hour format
    if period == "PM" and hours != 12:
        hours += 12
    elif period == "AM" and hours == 12:
        hours = 0
    
    # Format without leading zero
    return f"{hours}:{minutes:02d}"

def parse_golden_plan(golden_plan):
    """Parse the golden plan into structured itinerary format."""
    itinerary = []
    current_location = None
    
    for step in golden_plan:
        step = step.strip()
        if not step:
            continue
            
        # Parse start action
        if step.startswith("You start at"):
            match = re.search(r"You start at (.+?) at (.+?)\.", step)
            if match:
                current_location = match.group(1)
                start_time = convert_to_24hour(match.group(2))
                
        # Parse travel action
        elif "travel to" in step:
            match = re.search(r"You travel to (.+?) in (\d+) minutes and arrive at (.+?)\.", step)
            if match:
                current_location = match.group(1)
                arrival_time = convert_to_24hour(match.group(3))
                
        # Parse meet action
        elif "meet" in step and "for" in step:
            match = re.search(r"You meet (.+?) for (\d+) minutes from (.+?) to (.+?)\.", step)
            if match and current_location:
                person = match.group(1)
                start_time = convert_to_24hour(match.group(3))
                end_time = convert_to_24hour(match.group(4))
                
                itinerary.append({
                    "action": "meet",
                    "location": current_location,
                    "person": person,
                    "start_time": start_time,
                    "end_time": end_time
                })
                
    return itinerary

def compare_itineraries(model_itinerary, golden_itinerary):
    """Compare two itineraries and return True if they match exactly."""
    if len(model_itinerary) != len(golden_itinerary):
        return False
    
    for model_meet, golden_meet in zip(model_itinerary, golden_itinerary):
        # Skip if either meet is not a dictionary
        if not isinstance(model_meet, dict) or not isinstance(golden_meet, dict):
            return False
            
        # Check all required fields
        for field in ["action", "location", "person", "start_time", "end_time"]:
            if model_meet.get(field) != golden_meet.get(field):
                return False
    
    return True

def format_itinerary_compact(itinerary):
    """Convert itinerary to compact string representation for display."""
    parts = []
    
    for meeting in itinerary:
        if not isinstance(meeting, dict):
            continue
            
        action = meeting.get("action", "meet")
        location = meeting.get("location", "Unknown")
        person = meeting.get("person", "Unknown")
        start_time = meeting.get("start_time", "?")
        end_time = meeting.get("end_time", "?")
        
        parts.append(f"{action} {person} at {location} ({start_time}-{end_time})")
    
    return " → ".join(parts)

async def main():
    # Initialize state
    state = EvaluationState()
    state_loaded = state.load()

    # Determine file open mode
    txt_mode = 'a' if state_loaded and not state.first_run else 'w'
    json_mode = 'a' if state_loaded and not state.first_run else 'w'

    with open('O3-M-25-01-31_forceJSON_text_meeting_results.txt', txt_mode) as txt_file, \
         open('O3-M-25-01-31_forceJSON_text_meeting_results.json', json_mode) as json_file:
        
        # Write header if this is a fresh run
        if not state_loaded or state.first_run:
            json_file.write("")  # Will be properly initialized later
            state.first_run = False

        for example_id, example in meeting_examples.items():
            # Skip already processed examples
            if example_id in state.processed_examples:
                continue
                
            prompt = example['prompt_0shot']
            golden_plan = example['golden_plan']

            # Parse golden plan into structured format
            golden_itinerary = parse_golden_plan(golden_plan)

            # Modify prompt to request structured JSON output
            structured_prompt = (
                "You are an AI meeting planner and your task is to schedule meetings efficiently. "
                "Consider travel times and constraints carefully to optimize the schedule. "
                f"{prompt}\n\nPlease provide your meeting plan in the following exact JSON format:\n"
                "{\n"
                '  "itinerary": [\n'
                '    {"action": "meet", "location": "Location Name", "person": "Person Name", "start_time": "H:MM", "end_time": "H:MM"},\n'
                '    {"action": "meet", "location": "Location Name", "person": "Person Name", "start_time": "H:MM", "end_time": "H:MM"}\n'
                "  ]\n"
                "}\n"
                "Note: Times should be in 24-hour format without leading zeros (e.g., '9:30' not '09:30', '13:30' not '1:30PM')."
            )

            # Run the model with OpenAI API
            response = client.chat.completions.create(
                model=args.model,
                messages=[
                    {"role": "system", "content": "You are a helpful assistant that schedules meetings in JSON format."},
                    {"role": "user", "content": structured_prompt}
                ],
                response_format={"type": "json_object"}
            )

            model_response = response.choices[0].message.content
            
            try:
                model_data = json.loads(model_response)
                model_itinerary = model_data.get("itinerary", [])
                
                # Validate and clean each meeting in the itinerary
                cleaned_itinerary = []
                for meeting in model_itinerary:
                    if not isinstance(meeting, dict):
                        continue
                        
                    # Normalize action and location
                    action = meeting.get("action", "").lower()
                    if action != "meet":
                        continue
                        
                    location = meeting.get("location", "Unknown")
                    person = meeting.get("person", "Unknown")
                    
                    # Convert and validate times
                    start_time = meeting.get("start_time")
                    end_time = meeting.get("end_time")
                    
                    if start_time:
                        start_time = convert_to_24hour(start_time)
                    if end_time:
                        end_time = convert_to_24hour(end_time)
                    
                    if not start_time or not end_time:
                        continue
                        
                    cleaned_itinerary.append({
                        "action": action,
                        "location": location,
                        "person": person,
                        "start_time": start_time,
                        "end_time": end_time
                    })
                
                model_itinerary = cleaned_itinerary
                
            except json.JSONDecodeError as e:
                print(f"JSON decode error: {e}")
                model_itinerary = []

            # Compare with golden itinerary
            is_correct = compare_itineraries(model_itinerary, golden_itinerary)

            # Prepare result entry
            result_entry = {
                "final_program_time": {"itinerary": model_itinerary},
                "expected_time": {"itinerary": golden_itinerary},
                "count": example_id,
                "is_correct": is_correct
            }

            # Store results
            state.results_0shot.append(result_entry)

            # Format for display
            model_display = format_itinerary_compact(model_itinerary)
            golden_display = format_itinerary_compact(golden_itinerary)
            
            # Log output
            timestamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            output_line = (
                f"{example_id}. [{timestamp}] | Correct: {is_correct} | "
                f"ANSWER: {model_display} | EXPECTED: {golden_display}"
            )
            print(output_line)
            txt_file.write(f"{output_line}\n")

            # Save state after each example
            state.processed_examples.add(example_id)
            state.save()

        # Final results handling
        current_time = datetime.datetime.now()
        total_runtime = state.previous_time + (current_time - state.start_time)
        
        # Calculate accuracy
        correct_count = sum(1 for result in state.results_0shot if result["is_correct"])
        total_count = len(state.results_0shot)
        accuracy = correct_count / total_count if total_count > 0 else 0
        
        # Save final JSON results in the new format
        final_results = {
            "0shot": state.results_0shot,
            "metadata": {
                "model": args.model,
                "start_time": state.start_time.isoformat(),
                "end_time": current_time.isoformat(),
                "total_runtime_seconds": total_runtime.total_seconds(),
                "accuracy": accuracy,
                "correct_count": correct_count,
                "total_count": total_count
            }
        }
        json.dump(final_results, json_file, indent=4)

        # Final accuracy report
        txt_file.write("\n=== Final Results ===\n")
        txt_file.write(f"Model: {args.model}\n")
        txt_file.write(f"Start time: {state.start_time}\n")
        txt_file.write(f"End time: {current_time}\n")
        txt_file.write(f"Total runtime: {total_runtime}\n")
        txt_file.write(f"Accuracy: {correct_count}/{total_count} ({accuracy:.2%})\n")

    print("Processing complete. Results saved.")

if __name__ == "__main__":
    asyncio.run(main())

# import argparse
# import asyncio
# import json
# import datetime
# import re
# import os
# from openai import OpenAI

# # Read the API key from a file
# with open('/home/rma336/openai_research/openai_api_key.txt', 'r') as key_file:
#     api_key = key_file.read().strip()

# # Initialize the OpenAI client
# client = OpenAI(api_key=api_key)

# # Define the structured JSON schema for the meeting plan output
# JSON_SCHEMA = {
#     "name": "meeting_plan_schema",
#     "schema": {
#         "type": "object",
#         "properties": {
#             "itinerary": {
#                 "type": "array",
#                 "items": {
#                     "type": "object",
#                     "properties": {
#                         "action": {"type": "string", "enum": ["meet"]},
#                         "location": {"type": "string"},
#                         "person": {"type": "string"},
#                         "start_time": {"type": "string"},
#                         "end_time": {"type": "string"}
#                     },
#                     "required": ["action", "location", "person", "start_time", "end_time"]
#                 }
#             }
#         },
#         "required": ["itinerary"]
#     }
# }

# # Load the meeting planning examples from the JSON file
# with open('../../data/meeting_planning_100.json', 'r') as file:
#     meeting_examples = json.load(file)

# # Argument parser to select the model
# parser = argparse.ArgumentParser(description="Select an OpenAI model.")
# parser.add_argument('--model', type=str, required=True, help="The OpenAI model ID to use.")
# args = parser.parse_args()

# # State management
# STATE_FILE = "meeting_planning_state_openai.json"

# class EvaluationState:
#     def __init__(self):
#         self.results_0shot = []
#         self.processed_examples = set()
#         self.start_time = datetime.datetime.now()
#         self.previous_time = datetime.timedelta(0)
#         self.first_run = True

#     def save(self):
#         state_to_save = {
#             "results_0shot": self.results_0shot,
#             "processed_examples": list(self.processed_examples),
#             "start_time": self.start_time.isoformat(),
#             "previous_time": self.previous_time.total_seconds(),
#             "first_run": self.first_run
#         }
#         with open(STATE_FILE, 'w') as f:
#             json.dump(state_to_save, f)

#     def load(self):
#         try:
#             with open(STATE_FILE, 'r') as f:
#                 loaded = json.load(f)
#                 self.results_0shot = loaded["results_0shot"]
#                 self.processed_examples = set(loaded["processed_examples"])
#                 self.previous_time = datetime.timedelta(seconds=loaded["previous_time"])
#                 self.start_time = datetime.datetime.fromisoformat(loaded["start_time"])
#                 self.first_run = loaded.get("first_run", False)
#             return True
#         except (FileNotFoundError, json.JSONDecodeError, KeyError):
#             return False

# def convert_to_24hour(time_str):
#     """Convert time string to 24-hour format without leading zeros."""
#     time_str = time_str.replace(" ", "").upper()
    
#     if 'AM' not in time_str and 'PM' not in time_str:
#         try:
#             hours, minutes = map(int, time_str.split(':'))
#             if hours < 0 or hours > 23 or minutes < 0 or minutes > 59:
#                 return None
#             return f"{hours}:{minutes:02d}"
#         except:
#             return None
    
#     time_part = time_str[:-2]
#     period = time_str[-2:]
    
#     try:
#         if ':' in time_part:
#             hours, minutes = map(int, time_part.split(':'))
#         else:
#             hours = int(time_part)
#             minutes = 0
#     except:
#         return None
    
#     if hours < 0 or hours > 12 or minutes < 0 or minutes > 59:
#         return None
    
#     if period == "PM" and hours != 12:
#         hours += 12
#     elif period == "AM" and hours == 12:
#         hours = 0
    
#     return f"{hours}:{minutes:02d}"

# def parse_golden_plan(golden_plan):
#     """Parse the golden plan into structured itinerary format."""
#     itinerary = []
#     current_location = None
    
#     for step in golden_plan:
#         step = step.strip()
#         if not step:
#             continue
            
#         if step.startswith("You start at"):
#             match = re.search(r"You start at (.+?) at (.+?)\.", step)
#             if match:
#                 current_location = match.group(1)
#                 start_time = convert_to_24hour(match.group(2))
                
#         elif "travel to" in step:
#             match = re.search(r"You travel to (.+?) in (\d+) minutes and arrive at (.+?)\.", step)
#             if match:
#                 current_location = match.group(1)
#                 arrival_time = convert_to_24hour(match.group(3))
                
#         elif "meet" in step and "for" in step:
#             match = re.search(r"You meet (.+?) for (\d+) minutes from (.+?) to (.+?)\.", step)
#             if match and current_location:
#                 person = match.group(1)
#                 start_time = convert_to_24hour(match.group(3))
#                 end_time = convert_to_24hour(match.group(4))
                
#                 itinerary.append({
#                     "action": "meet",
#                     "location": current_location,
#                     "person": person,
#                     "start_time": start_time,
#                     "end_time": end_time
#                 })
                
#     return itinerary

# def compare_itineraries(model_itinerary, golden_itinerary):
#     """Compare two itineraries and return True if they match exactly."""
#     if len(model_itinerary) != len(golden_itinerary):
#         return False
    
#     for model_meet, golden_meet in zip(model_itinerary, golden_itinerary):
#         if not isinstance(model_meet, dict) or not isinstance(golden_meet, dict):
#             return False
            
#         for field in ["action", "location", "person", "start_time", "end_time"]:
#             if model_meet.get(field) != golden_meet.get(field):
#                 return False
    
#     return True

# def format_itinerary_compact(itinerary):
#     """Convert itinerary to compact string representation for display."""
#     parts = []
    
#     for meeting in itinerary:
#         if not isinstance(meeting, dict):
#             continue
            
#         action = meeting.get("action", "meet")
#         location = meeting.get("location", "Unknown")
#         person = meeting.get("person", "Unknown")
#         start_time = meeting.get("start_time", "?")
#         end_time = meeting.get("end_time", "?")
        
#         parts.append(f"{action} {person} at {location} ({start_time}-{end_time})")
    
#     return " → ".join(parts)

# def create_batch_requests(examples, model):
#     """Create batch requests for all unprocessed examples."""
#     batch_requests = []
    
#     for example_id, example in examples.items():
#         prompt = example['prompt_0shot']
        
#         structured_prompt = (
#             "You are an AI meeting planner and your task is to schedule meetings efficiently. "
#             "Consider travel times and constraints carefully to optimize the schedule. "
#             f"{prompt}\n\nPlease provide your meeting plan in the following exact JSON format:\n"
#             "{\n"
#             '  "itinerary": [\n'
#             '    {"action": "meet", "location": "Location Name", "person": "Person Name", "start_time": "H:MM", "end_time": "H:MM"},\n'
#             '    {"action": "meet", "location": "Location Name", "person": "Person Name", "start_time": "H:MM", "end_time": "H:MM"}\n'
#             "  ]\n"
#             "}\n"
#             "Note: Times should be in 24-hour format without leading zeros (e.g., '9:30' not '09:30', '13:30' not '1:30PM')."
#         )
        
#         batch_requests.append({
#             "custom_id": example_id,
#             "method": "POST",
#             "url": "/v1/chat/completions",
#             "body": {
#                 "model": model,
#                 "messages": [
#                     {"role": "system", "content": "You are a helpful assistant that schedules meetings in JSON format."},
#                     {"role": "user", "content": structured_prompt}
#                 ],
#                 "response_format": {"type": "json_object"},
#                 "max_tokens": 1000
#             }
#         })
    
#     return batch_requests

# async def main():
#     # Initialize state
#     state = EvaluationState()
#     state_loaded = state.load()

#     # Determine file open mode
#     txt_mode = 'a' if state_loaded and not state.first_run else 'w'
#     json_mode = 'a' if state_loaded and not state.first_run else 'w'

#     with open('O3-M-25-01-31_forceJSON_text_meeting_results.txt', txt_mode) as txt_file, \
#          open('O3-M-25-01-31_forceJSON_text_meeting_results.json', json_mode) as json_file:
        
#         if not state_loaded or state.first_run:
#             json_file.write("")
#             state.first_run = False

#         # Filter out already processed examples
#         unprocessed_examples = {k: v for k, v in meeting_examples.items() if k not in state.processed_examples}
        
#         if not unprocessed_examples:
#             print("All examples already processed.")
#             return

#         # Create batch requests
#         batch_requests = create_batch_requests(unprocessed_examples, args.model)
        
#         # Create batch input jsonl file
#         jsonl_path = "batch_input.jsonl"
#         with open(jsonl_path, "w") as f:
#             for request in batch_requests:
#                 f.write(json.dumps(request, ensure_ascii=False) + "\n")

#         # Create batch input file for OpenAI server
#         batch_input_file = client.files.create(
#             file=open(jsonl_path, "rb"),
#             purpose="batch"
#         )
        
#         # Create batch job
#         batch_job = client.batches.create(
#             input_file_id=batch_input_file.id,
#             endpoint="/v1/chat/completions",
#             completion_window="24h",
#             metadata={
#                 "description": "Meeting planning evaluation"
#             }
#         )
        
#         print(f"Submitted batch job with ID: {batch_job.id}")
#         print("Waiting for batch job to complete...")
        
#         # Wait for batch job to complete
#         while True:
#             batch_status = client.batches.retrieve(batch_job.id)
#             if batch_status.status == "completed":
#                 break
#             elif batch_status.status in ("failed", "cancelled"):
#                 print(f"Batch job {batch_status.status}")
#                 return
#             await asyncio.sleep(60)  # Check every minute
        
#         # Get results
#         result_file_id = batch_status.output_file_id
#         if not result_file_id:
#             print("Error: No output file ID found")
#             return
            
#         results_content = client.files.content(result_file_id).content.decode('utf-8')
#         results = [json.loads(line) for line in results_content.split('\n') if line]
        
#         # Process results
#         for result in results:
#             example_id = result['custom_id']
#             example = meeting_examples[example_id]
#             golden_plan = example['golden_plan']
#             golden_itinerary = parse_golden_plan(golden_plan)
            
#             try:
#                 response = result['response']['body']
#                 model_response = response['choices'][0]['message']['content']
#                 model_data = json.loads(model_response)
#                 model_itinerary = model_data.get("itinerary", [])
                
#                 # Clean and validate itinerary
#                 cleaned_itinerary = []
#                 for meeting in model_itinerary:
#                     if not isinstance(meeting, dict):
#                         continue
                        
#                     action = meeting.get("action", "").lower()
#                     if action != "meet":
#                         continue
                        
#                     location = meeting.get("location", "Unknown")
#                     person = meeting.get("person", "Unknown")
#                     start_time = convert_to_24hour(meeting.get("start_time"))
#                     end_time = convert_to_24hour(meeting.get("end_time"))
                    
#                     if not start_time or not end_time:
#                         continue
                        
#                     cleaned_itinerary.append({
#                         "action": action,
#                         "location": location,
#                         "person": person,
#                         "start_time": start_time,
#                         "end_time": end_time
#                     })
                
#                 model_itinerary = cleaned_itinerary
                
#             except (json.JSONDecodeError, KeyError) as e:
#                 print(f"Error processing example {example_id}: {e}")
#                 model_itinerary = []

#             # Compare with golden itinerary
#             is_correct = compare_itineraries(model_itinerary, golden_itinerary)

#             # Prepare result entry
#             result_entry = {
#                 "final_program_time": {"itinerary": model_itinerary},
#                 "expected_time": {"itinerary": golden_itinerary},
#                 "count": example_id,
#                 "is_correct": is_correct
#             }

#             # Store results
#             state.results_0shot.append(result_entry)

#             # Format for display
#             model_display = format_itinerary_compact(model_itinerary)
#             golden_display = format_itinerary_compact(golden_itinerary)
            
#             # Log output
#             timestamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
#             output_line = (
#                 f"{example_id}. [{timestamp}] | Correct: {is_correct} | "
#                 f"ANSWER: {model_display} | EXPECTED: {golden_display}"
#             )
#             print(output_line)
#             txt_file.write(f"{output_line}\n")

#             # Save state after each example
#             state.processed_examples.add(example_id)
#             state.save()

#         # Final results handling
#         current_time = datetime.datetime.now()
#         total_runtime = state.previous_time + (current_time - state.start_time)
        
#         # Calculate accuracy
#         correct_count = sum(1 for result in state.results_0shot if result["is_correct"])
#         total_count = len(state.results_0shot)
#         accuracy = correct_count / total_count if total_count > 0 else 0
        
#         # Save final JSON results in the new format
#         final_results = {
#             "0shot": state.results_0shot,
#             "metadata": {
#                 "model": args.model,
#                 "start_time": state.start_time.isoformat(),
#                 "end_time": current_time.isoformat(),
#                 "total_runtime_seconds": total_runtime.total_seconds(),
#                 "accuracy": accuracy,
#                 "correct_count": correct_count,
#                 "total_count": total_count
#             }
#         }
#         json.dump(final_results, json_file, indent=4)

#         # Final accuracy report
#         txt_file.write("\n=== Final Results ===\n")
#         txt_file.write(f"Model: {args.model}\n")
#         txt_file.write(f"Start time: {state.start_time}\n")
#         txt_file.write(f"End time: {current_time}\n")
#         txt_file.write(f"Total runtime: {total_runtime}\n")
#         txt_file.write(f"Accuracy: {correct_count}/{total_count} ({accuracy:.2%})\n")

#     print("Processing complete. Results saved.")

# if __name__ == "__main__":
#     asyncio.run(main())



# # #**********WORKING CODE, FORCE JSON, TEXT OUTPUTS, MEETING PLANNING, OPENAI, CHECKPOINT************

# import argparse
# import asyncio
# import json
# import datetime
# import re
# from openai import OpenAI

# # Read the API key from a file
# with open('/home/rma336/openai_research/openai_api_key.txt', 'r') as key_file:
#     api_key = key_file.read().strip()

# # Initialize the OpenAI client
# client = OpenAI(api_key=api_key)

# # Define the structured JSON schema for the meeting plan output
# JSON_SCHEMA = {
#     "name": "meeting_plan_schema",
#     "schema": {
#         "type": "object",
#         "properties": {
#             "schedule": {
#                 "type": "array",
#                 "items": {
#                     "type": "object",
#                     "properties": {
#                         "action": {"type": "string", "enum": ["start", "travel", "wait", "meet"]},
#                         "location": {"type": "string"},
#                         "time": {"type": "string"},
#                         "duration": {"type": "number", "minimum": 0},
#                         "to": {"type": "string"}  # only for travel actions
#                     },
#                     "required": ["action", "location"],
#                     "anyOf": [
#                         {
#                             "properties": {
#                                 "action": {"const": "start"}
#                             },
#                             "required": ["time"]
#                         },
#                         {
#                             "properties": {
#                                 "action": {"const": "travel"}
#                             },
#                             "required": ["duration", "to"]
#                         },
#                         {
#                             "properties": {
#                                 "action": {"const": "wait"}
#                             },
#                             "required": ["time"]
#                         },
#                         {
#                             "properties": {
#                                 "action": {"const": "meet"}
#                             },
#                             "required": ["duration"]
#                         }
#                     ]
#                 }
#             }
#         },
#         "required": ["schedule"]
#     }
# }

# # Load the meeting planning examples from the JSON file
# with open('../../data/meeting_planning_100.json', 'r') as file:
#     meeting_examples = json.load(file)

# # Argument parser to select the model
# parser = argparse.ArgumentParser(description="Select an OpenAI model.")
# parser.add_argument('--model', type=str, required=True, help="The OpenAI model ID to use.")
# args = parser.parse_args()

# # State management
# STATE_FILE = "meeting_planning_state_openai.json"

# class EvaluationState:
#     def __init__(self):
#         self.correct_0shot = 0
#         # self.correct_5shot = 0
#         self.total_0shot = 0
#         # self.total_5shot = 0
#         self.results_0shot = []
#         # self.results_5shot = []
#         self.processed_examples = set()
#         self.start_time = datetime.datetime.now()
#         self.previous_time = datetime.timedelta(0)
#         self.first_run = True

#     def save(self):
#         state_to_save = {
#             "correct_0shot": self.correct_0shot,
#             # "correct_5shot": self.correct_5shot,
#             "total_0shot": self.total_0shot,
#             # "total_5shot": self.total_5shot,
#             "results_0shot": self.results_0shot,
#             # "results_5shot": self.results_5shot,
#             "processed_examples": list(self.processed_examples),
#             "start_time": self.start_time.isoformat(),
#             "previous_time": self.previous_time.total_seconds(),
#             "first_run": self.first_run
#         }
#         with open(STATE_FILE, 'w') as f:
#             json.dump(state_to_save, f)

#     def load(self):
#         try:
#             with open(STATE_FILE, 'r') as f:
#                 loaded = json.load(f)
#                 self.correct_0shot = loaded["correct_0shot"]
#                 # self.correct_5shot = loaded["correct_5shot"]
#                 self.total_0shot = loaded["total_0shot"]
#                 # self.total_5shot = loaded["total_5shot"]
#                 self.results_0shot = loaded["results_0shot"]
#                 # self.results_5shot = loaded["results_5shot"]
#                 self.processed_examples = set(loaded["processed_examples"])
#                 self.previous_time = datetime.timedelta(seconds=loaded["previous_time"])
#                 self.start_time = datetime.datetime.fromisoformat(loaded["start_time"])
#                 self.first_run = loaded.get("first_run", False)
#             return True
#         except (FileNotFoundError, json.JSONDecodeError, KeyError):
#             return False

# def remove_leading_zero_from_time(time_str):
#     """Remove leading zero from the time string if the hour is a single digit."""
#     # Handle both "HH:MMAM/PM" and "HH:MM AM/PM" formats
#     time_str = time_str.replace(" ", "")
#     time_part, period = time_str[:-2], time_str[-2:].upper()
    
#     time_parts = time_part.split(":")
#     if len(time_parts[0]) == 2 and time_parts[0][0] == "0":
#         time_parts[0] = time_parts[0][1]  # Remove leading zero
    
#     return f"{':'.join(time_parts)}{period}"

# def parse_golden_plan(golden_plan):
#     """Parse the golden plan into structured schedule format matching our JSON schema."""
#     schedule = []
#     last_time = None  # Track the last time encountered
    
#     for step in golden_plan:
#         step = step.strip()
#         if not step:
#             continue
            
#         # Parse start action
#         if step.startswith("You start at"):
#             match = re.search(r"You start at (.+?) at (.+?)\.", step)
#             if match:
#                 time = remove_leading_zero_from_time(match.group(2))
#                 schedule.append({
#                     "action": "start",
#                     "location": match.group(1),
#                     "time": time
#                 })
#                 last_time = time
                
#         # Parse travel action
#         elif "travel to" in step:
#             match = re.search(r"You travel to (.+?) in (\d+) minutes and arrive at (.+?)\.", step)
#             if match:
#                 time = remove_leading_zero_from_time(match.group(3))
#                 schedule.append({
#                     "action": "travel",
#                     "location": match.group(1),
#                     "duration": int(match.group(2)),
#                     "time": time,
#                     "to": match.group(1)
#                 })
#                 last_time = time
                
#         # Parse wait action
#         elif "wait until" in step:
#             match = re.search(r"You wait until (.+?)\.", step)
#             if match:
#                 time = remove_leading_zero_from_time(match.group(1))
#                 schedule.append({
#                     "action": "wait",
#                     "location": schedule[-1]["location"] if schedule else "Unknown",
#                     "time": time
#                 })
#                 last_time = time
                
#         # Parse meet action
#         elif "meet" in step and "for" in step:
#             match = re.search(r"You meet (.+?) for (\d+) minutes from (.+?) to (.+?)\.", step)
#             if match:
#                 time = remove_leading_zero_from_time(match.group(3))
#                 schedule.append({
#                     "action": "meet",
#                     "location": schedule[-1]["location"] if schedule else "Unknown",
#                     "duration": int(match.group(2)),
#                     "time": time
#                 })
#                 last_time = time
                
#     return schedule

# def compare_schedules(model_schedule, golden_schedule):
#     """Compare two schedules and return True if they match exactly."""
#     if len(model_schedule) != len(golden_schedule):
#         return False
    
#     for model_step, golden_step in zip(model_schedule, golden_schedule):
#         # Skip if either step is not a dictionary
#         if not isinstance(model_step, dict) or not isinstance(golden_step, dict):
#             return False
            
#         # Check action type matches
#         if model_step.get("action") != golden_step.get("action"):
#             return False
            
#         # Check common fields
#         if model_step.get("location") != golden_step.get("location"):
#             return False
            
#         # Action-specific checks with time normalization
#         if model_step.get("action") == "travel":
#             if model_step.get("duration") != golden_step.get("duration"):
#                 return False
#             if model_step.get("to") != golden_step.get("to"):
#                 return False
#         elif model_step.get("action") == "meet":
#             if model_step.get("duration") != golden_step.get("duration"):
#                 return False
        
#         # Time comparison for all actions that have time
#         if 'time' in model_step and 'time' in golden_step:
#             model_time = remove_leading_zero_from_time(model_step['time'])
#             golden_time = remove_leading_zero_from_time(golden_step['time'])
#             if model_time != golden_time:
#                 return False
#         elif 'time' in model_step or 'time' in golden_step:
#             # One has time but the other doesn't
#             return False
    
#     return True

# def format_schedule_compact(schedule):
#     """Convert schedule to compact string representation for display."""
#     parts = []
#     last_time = None
    
#     for step in schedule:
#         if not isinstance(step, dict):
#             continue
            
#         action = step.get("action")
#         location = step.get("location", "Unknown")
        
#         if action == "start":
#             time = remove_leading_zero_from_time(step.get('time', '')) if 'time' in step else 'Unknown'
#             parts.append(f"Start at {location} at {time}")
#             last_time = time if 'time' in step else last_time
#         elif action == "travel":
#             duration = step.get('duration', '?')
#             time = remove_leading_zero_from_time(step.get('time', '')) if 'time' in step else 'Unknown'
#             parts.append(f"Travel to {location} ({duration}min)")
#             last_time = time if 'time' in step else last_time
#         elif action == "wait":
#             time = remove_leading_zero_from_time(step.get('time', '')) if 'time' in step else 'Unknown'
#             parts.append(f"Wait until {time}")
#             last_time = time if 'time' in step else last_time
#         elif action == "meet":
#             duration = step.get('duration', '?')
#             meet_time = remove_leading_zero_from_time(step.get('time', last_time if last_time else ''))
#             parts.append(f"Meet for {duration}min at {meet_time}")
#             last_time = meet_time
    
#     return " → ".join(parts)

# async def main():
#     # Initialize state
#     state = EvaluationState()
#     state_loaded = state.load()

#     # Determine file open mode
#     txt_mode = 'a' if state_loaded and not state.first_run else 'w'
#     json_mode = 'a' if state_loaded and not state.first_run else 'w'

#     with open('GPT-4O-M-24-07-18_forceJSON_text_meeting_results.txt', txt_mode) as txt_file, \
#          open('GPT-4O-M-24-07-18_forceJSON_text_meeting_results.json', json_mode) as json_file:
        
#         # Write header if this is a fresh run
#         if not state_loaded or state.first_run:
#             json_file.write("")  # Will be properly initialized later
#             state.first_run = False

#         for example_id, example in meeting_examples.items():
#             # Skip already processed examples
#             if example_id in state.processed_examples:
#                 continue
                
#             for prompt_type in ['prompt_0shot']:
#                 prompt = example[prompt_type]
#                 golden_plan = example['golden_plan']

#                 # Parse golden plan into structured format
#                 golden_schedule = parse_golden_plan(golden_plan)

#                 # Modify prompt to request structured JSON output
#                 structured_prompt = (
#                     "You are an AI meeting planner and your task is to schedule meetings efficiently. "
#                     "Consider travel times and constraints carefully to optimize the schedule. "
#                     f"{prompt}\n\nPlease provide your meeting plan in the following exact JSON format:\n"
#                     "{\n"
#                     '  "schedule": [\n'
#                     '    {"action": "start", "location": "Location Name", "time": "H:MMAM/PM"},\n'
#                     '    {"action": "travel", "location": "Destination", "duration": X, "time": "H:MMAM/PM", "to": "Destination"},\n'
#                     '    {"action": "wait", "location": "Location Name", "time": "H:MMAM/PM"},\n'
#                     '    {"action": "meet", "location": "Location Name", "duration": X, "time": "H:MMAM/PM"}\n'
#                     "  ]\n"
#                     "}\n"
#                     "Note: Times should be in format like '9:00AM' (no leading zero) and durations in minutes."
#                 )

#                 # Run the model with OpenAI API
#                 response = client.chat.completions.create(
#                     model=args.model,
#                     messages=[
#                         {"role": "system", "content": "You are a helpful assistant that schedules meetings in JSON format."},
#                         {"role": "user", "content": structured_prompt}
#                     ],
#                     response_format={"type": "json_object"}
#                 )

#                 model_response = response.choices[0].message.content
                
#                 try:
#                     model_data = json.loads(model_response)
#                     model_schedule = model_data.get("schedule", [])
                    
#                     # Validate and clean each step in the schedule
#                     cleaned_schedule = []
#                     last_time = None
#                     for step in model_schedule:
#                         if not isinstance(step, dict):
#                             continue
                            
#                         # Normalize action and location
#                         action = step.get("action", "").lower()
#                         location = step.get("location", "Unknown")
                        
#                         # Handle time formatting
#                         time = step.get("time")
#                         if time:
#                             try:
#                                 time = remove_leading_zero_from_time(time)
#                             except:
#                                 time = None
                        
#                         # Create cleaned step
#                         cleaned_step = {"action": action, "location": location}
#                         if time:
#                             cleaned_step["time"] = time
#                             last_time = time
                        
#                         # Add action-specific fields
#                         if action == "travel":
#                             cleaned_step["duration"] = step.get("duration", 0)
#                             cleaned_step["to"] = step.get("to", location)
#                             if "time" in step:
#                                 last_time = time
#                         elif action == "meet":
#                             cleaned_step["duration"] = step.get("duration", 0)
#                             if "time" not in cleaned_step and last_time:
#                                 cleaned_step["time"] = last_time
                        
#                         cleaned_schedule.append(cleaned_step)
                    
#                     model_schedule = cleaned_schedule
                    
#                 except json.JSONDecodeError as e:
#                     print(f"JSON decode error: {e}")
#                     model_schedule = []

#                 # Compare with golden schedule
#                 is_correct = compare_schedules(model_schedule, golden_schedule)

#                 # Update state
#                 if prompt_type == 'prompt_0shot':
#                     state.total_0shot += 1
#                     if is_correct:
#                         state.correct_0shot += 1
#                 # else:
#                 #     state.total_5shot += 1
#                 #     if is_correct:
#                 #         state.correct_5shot += 1

#                 # Prepare result entry
#                 result_entry = {
#                     "example_id": example_id,
#                     "prompt_type": prompt_type,
#                     "model_response": model_response,
#                     "model_schedule": model_schedule,
#                     "golden_schedule": golden_schedule,
#                     "is_correct": is_correct,
#                     "timestamp": datetime.datetime.now().isoformat()
#                 }

#                 # Store results
#                 if prompt_type == 'prompt_0shot':
#                     state.results_0shot.append(result_entry)
#                 # else:
#                 #     state.results_5shot.append(result_entry)

#                 # Format for display
#                 model_display = format_schedule_compact(model_schedule)
#                 golden_display = format_schedule_compact(golden_schedule)
                
#                 # Log output
#                 timestamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
#                 output_line = (
#                     f"{example_id}. [{timestamp}] | {prompt_type} | Correct: {is_correct} | "
#                     f"ANSWER: {model_display} | EXPECTED: {golden_display}"
#                 )
#                 print(output_line)
#                 txt_file.write(f"{output_line}\n")

#                 # Save state after each prompt type
#                 state.processed_examples.add(example_id)
#                 state.save()

#         # Final results handling
#         current_time = datetime.datetime.now()
#         total_runtime = state.previous_time + (current_time - state.start_time)
        
#         # Save final JSON results
#         final_results = {
#             "model": args.model,
#             "start_time": state.start_time.isoformat(),
#             "end_time": current_time.isoformat(),
#             "total_runtime_seconds": total_runtime.total_seconds(),
#             "results": {
#                 "0shot": state.results_0shot
#                 # "5shot": state.results_5shot
#             },
#             "accuracy": {
#                 "0shot": state.correct_0shot / state.total_0shot if state.total_0shot > 0 else 0
#                 # "5shot": state.correct_5shot / state.total_5shot if state.total_5shot > 0 else 0,
#                 # "total": (state.correct_0shot + state.correct_5shot) / (state.total_0shot + state.total_5shot) if (state.total_0shot + state.total_5shot) > 0 else 0
#             }
#         }
#         json.dump(final_results, json_file, indent=4)

#         # Final accuracy report
#         txt_file.write("\n=== Final Results ===\n")
#         txt_file.write(f"Model: {args.model}\n")
#         txt_file.write(f"Start time: {state.start_time}\n")
#         txt_file.write(f"End time: {current_time}\n")
#         txt_file.write(f"Total runtime: {total_runtime}\n")
#         txt_file.write(f"0-shot accuracy: {state.correct_0shot}/{state.total_0shot} ({state.correct_0shot/state.total_0shot:.2%})\n")
#         # txt_file.write(f"5-shot accuracy: {state.correct_5shot}/{state.total_5shot} ({state.correct_5shot/state.total_5shot:.2%})\n")
#         # txt_file.write(f"Total accuracy: {state.correct_0shot + state.correct_5shot}/{state.total_0shot + state.total_5shot} ({(state.correct_0shot + state.correct_5shot)/(state.total_0shot + state.total_5shot):.2%})\n")

#     print("Processing complete. Results saved.")

# if __name__ == "__main__":
#     asyncio.run(main())


