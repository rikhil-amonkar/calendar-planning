import argparse
import asyncio
import json
import datetime
import logging
import re
import subprocess
import os
import torch
import gc
from openai import OpenAI

# Configure logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')

# Read the API key from a file
with open('/home/rma336/openai_research/openai_api_key.txt', 'r') as key_file:
    api_key = key_file.read().strip()

# Initialize the OpenAI client
openai_client = OpenAI(api_key=api_key)

# Argument parser to select the model
parser = argparse.ArgumentParser(description="Select an OpenAI model.")
parser.add_argument('--model', type=str, required=True, help="The OpenAI model ID to use (e.g., gpt-4, gpt-3.5-turbo)")
args = parser.parse_args()

# State management
STATE_FILE = "meeting_planning_state_openai_code_quick.json"

class EvaluationState:
    def __init__(self):
        self.expected_outputs_0shot = []
        self.predicted_outputs_0shot = []
        self.start_time = datetime.datetime.now()
        self.no_error_count_0shot = 0
        self.correct_output_count_0shot = 0
        self.processed_examples = set()
        self.previous_time = 0
        self.first_run = True

    def save(self):
        state_to_save = {
            "expected_outputs_0shot": self.expected_outputs_0shot,
            "predicted_outputs_0shot": self.predicted_outputs_0shot,
            "start_time": self.start_time.isoformat(),
            "no_error_count_0shot": self.no_error_count_0shot,
            "correct_output_count_0shot": self.correct_output_count_0shot,
            "processed_examples": list(self.processed_examples),
            "previous_time": self.previous_time,
            "first_run": self.first_run
        }
        with open(STATE_FILE, 'w') as f:
            json.dump(state_to_save, f)

    def load(self):
        try:
            with open(STATE_FILE, 'r') as f:
                loaded = json.load(f)
                self.expected_outputs_0shot = loaded["expected_outputs_0shot"]
                self.predicted_outputs_0shot = loaded["predicted_outputs_0shot"]
                self.no_error_count_0shot = loaded["no_error_count_0shot"]
                self.correct_output_count_0shot = loaded["correct_output_count_0shot"]
                self.processed_examples = set(loaded["processed_examples"])
                self.previous_time = loaded["previous_time"]
                self.start_time = datetime.datetime.fromisoformat(loaded["start_time"])
                self.first_run = loaded.get("first_run", False)
            return True
        except (FileNotFoundError, json.JSONDecodeError, KeyError):
            return False

# Load the meeting planning examples from the JSON file
with open('../../data/meeting_planning_100.json', 'r') as file:
    meeting_examples = json.load(file)

# Define prefix and suffix messages for code generation
prefix_message = (
    "You are an expert computational meeting planner. Your task is to write a Python program that "
    "algorithmically calculates the optimal meeting schedule based on the participants' constraints.\n"
    "The program must actually compute the plan using the given parameters, not just print a pre-determined answer.\n"
    "Input parameters:\n"
)

suffix_message = (
    "\n\nGenerate a complete, self-contained Python program that:\n"
    "1. Takes the above meeting constraints as input variables\n"
    "2. Computes the optimal meeting schedule using logical rules and calculations\n"
    "3. Outputs the result as a JSON-formatted dictionary with the following structure:\n"
    "{\n"
    '  "itinerary": [\n'
    '    {"action": "meet", "location": "Location Name", "person": "Person Name", "start_time": "H:MM", "end_time": "H:MM"},\n'
    '    {"action": "meet", "location": "Location Name", "person": "Person Name", "start_time": "H:MM", "end_time": "H:MM"}\n'
    "  ]\n"
    "}\n"
    "Rules for the program:\n"
    "- Times should be in 24-hour format like '9:00' or '13:30' (no leading zero)\n"
    "- The schedule must account for all travel times and constraints\n"
    "- The program must actually compute the schedule, not just print a static answer\n"
    "\n"
    "Output only the complete Python code with no additional text or explanation.\n"
    "The code must run independently and output valid JSON when executed."
)

def extract_code(response):
    """Extract Python code from a response, completely removing any markdown delimiters."""
    if not response:
        return None
        
    response = response.strip()
    
    # First handle SOLUTION: prefix
    if response.startswith("SOLUTION:"):
        response = response[len("SOLUTION:"):].strip()
    
    # Then handle markdown code blocks (```python or ```)
    if response.startswith("```python"):
        end = response.find("```", 9)
        if end != -1:
            return response[9:end].strip()
    elif response.startswith("```"):
        end = response.find("```", 3)
        if end != -1:
            return response[3:end].strip()
    
    # Handle other cases
    python_indicators = [
        "#!/usr/bin/env python",
        "if __name__ == \"__main__\":",
        "def main():",
        "import ",
        "from ",
        "print(",
        "def ",
        "class ",
        "return ",
        " = "
    ]
    
    # Count Python indicators
    indicator_count = sum(1 for indicator in python_indicators if indicator in response)
    
    if indicator_count >= 3 and '\n' in response:
        return response.strip()
    
    return None

def run_generated_code(code):
    try:
        with open("generated_code_openai_code_quick.py", "w") as file:
            file.write(code)
        result = subprocess.run(["python", "generated_code_openai_code_quick.py"], capture_output=True, text=True, check=True)
        output = result.stdout.strip()
        return output, False  # No error occurred
    except subprocess.CalledProcessError as e:
        return None, True  # Error occurred

def convert_to_24hr_no_leading_zero(time_str):
    """Convert time string to 24-hour format without leading zeros."""
    if not time_str:
        return ""
    
    try:
        # Remove any spaces and make uppercase
        time_str = time_str.strip().replace(" ", "").upper()
        time_part = time_str
        
        # Check for AM/PM
        period = None
        if "AM" in time_str:
            period = "AM"
            time_part = time_str.replace("AM", "")
        elif "PM" in time_str:
            period = "PM"
            time_part = time_str.replace("PM", "")
        
        # Split hours and minutes
        if ":" in time_part:
            hours, minutes = time_part.split(":")
        else:
            hours = time_part
            minutes = "00"
        
        # Convert to integer hours
        hours = int(hours)
        
        # Apply 24-hour conversion if period exists
        if period == "PM" and hours != 12:
            hours += 12
        elif period == "AM" and hours == 12:
            hours = 0
        
        # Format without leading zeros
        return f"{hours}:{minutes}"
    
    except Exception as e:
        logging.error(f"Error converting time string '{time_str}': {e}")
        return ""

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
                start_time = convert_to_24hr_no_leading_zero(match.group(2))
                
        # Parse travel action
        elif "travel to" in step:
            match = re.search(r"You travel to (.+?) in (\d+) minutes and arrive at (.+?)\.", step)
            if match:
                current_location = match.group(1)
                arrival_time = convert_to_24hr_no_leading_zero(match.group(3))
                
        # Parse meet action
        elif "meet" in step and "for" in step:
            match = re.search(r"You meet (.+?) for (\d+) minutes from (.+?) to (.+?)\.", step)
            if match and current_location:
                person = match.group(1)
                start_time = convert_to_24hr_no_leading_zero(match.group(3))
                end_time = convert_to_24hr_no_leading_zero(match.group(4))
                
                itinerary.append({
                    "action": "meet",
                    "location": current_location,
                    "person": person,
                    "start_time": start_time,
                    "end_time": end_time
                })
                
    return itinerary

def parse_model_output(model_output):
    """Parse the model's JSON output into structured itinerary format."""
    if not model_output:
        return None
    
    # If we already have a dictionary (from direct code execution), just normalize it
    if isinstance(model_output, dict):
        return normalize_itinerary(model_output)
    
    # Handle SOLUTION: prefix case - extract the actual content
    if isinstance(model_output, str):
        model_output = model_output.strip()
        if model_output.startswith("SOLUTION:"):
            model_output = model_output[len("SOLUTION:"):].strip()
    
    # First try to parse the output directly as JSON (in case it's just the JSON)
    try:
        if isinstance(model_output, str):
            itinerary_data = json.loads(model_output)
            return normalize_itinerary(itinerary_data)
    except json.JSONDecodeError:
        pass
    
    # If direct JSON parsing fails, look for JSON in print output
    json_pattern = r'\{.*?"itinerary"\s*:\s*\[.*?\]\}'
    matches = re.search(json_pattern, model_output, re.DOTALL)
    if matches:
        try:
            itinerary_data = json.loads(matches.group(0))
            return normalize_itinerary(itinerary_data)
        except json.JSONDecodeError:
            pass
    
    # If we still haven't found JSON, try to find the last dictionary-looking structure
    dict_pattern = r'\{[\s\S]*?\}'
    matches = re.findall(dict_pattern, model_output)
    if matches:
        # Try each match from last to first (most likely the output is at the end)
        for match in reversed(matches):
            try:
                itinerary_data = json.loads(match)
                if "itinerary" in itinerary_data:
                    return normalize_itinerary(itinerary_data)
            except json.JSONDecodeError:
                continue
    
    return None

def normalize_itinerary(itinerary_data):
    """Normalize the itinerary data into our standard format."""
    if not isinstance(itinerary_data, dict) or "itinerary" not in itinerary_data:
        return None
    
    itinerary = itinerary_data.get("itinerary", [])
    normalized_itinerary = []
    
    for step in itinerary:
        if not isinstance(step, dict):
            continue
            
        # Normalize action and location
        action = step.get("action", "").lower()
        if action != "meet":
            continue  # We only care about meet actions in this format
            
        location = step.get("location", "Unknown")
        person = step.get("person", "Unknown")
        
        # Handle time formatting
        start_time = convert_to_24hr_no_leading_zero(step.get("start_time", ""))
        end_time = convert_to_24hr_no_leading_zero(step.get("end_time", ""))
        
        # Create cleaned step
        normalized_step = {
            "action": action,
            "location": location,
            "person": person,
            "start_time": start_time,
            "end_time": end_time
        }
        
        normalized_itinerary.append(normalized_step)
    
    return normalized_itinerary

def format_itinerary_compact(itinerary):
    """Convert itinerary to compact string representation for display."""
    if not itinerary:
        return "None"
    
    parts = []
    
    for step in itinerary:
        if not isinstance(step, dict):
            continue
            
        action = step.get("action")
        location = step.get("location", "Unknown")
        person = step.get("person", "Unknown")
        start_time = step.get("start_time", "?:??")
        end_time = step.get("end_time", "?:??")
        
        if action == "meet":
            parts.append(f"Meet {person} at {location} ({start_time}-{end_time})")
    
    return " → ".join(parts)

async def main():
    # Initialize state
    state = EvaluationState()
    state_loaded = state.load()

    # Determine file open mode
    txt_mode = 'a' if state_loaded and not state.first_run else 'w'

    # Ensure the JSON file exists with the correct structure
    if not os.path.exists("O3-M-25-01-31_code_meeting_results.json") or not state_loaded:
        with open("O3-M-25-01-31_code_meeting_results.json", "w") as json_file:
            json.dump({"0shot": []}, json_file, indent=4)

    with open("O3-M-25-01-31_code_meeting_results.txt", txt_mode) as txt_file:
        # Write header if this is a fresh run
        if not state_loaded or state.first_run:
            with open("O3-M-25-01-31_code_meeting_results.json", "w") as json_file:
                json.dump({"0shot": []}, json_file, indent=4)
            state.first_run = False

        for example_id, example in meeting_examples.items():
            # Skip already processed examples
            if example_id in state.processed_examples:
                continue
                
            prompt = example["prompt_0shot"]
            golden_plan = example["golden_plan"]
            full_prompt = prefix_message + prompt + suffix_message
            correct_status = False

            try:
                # Use OpenAI API directly
                response = openai_client.chat.completions.create(
                    model=args.model,
                    messages=[
                        {"role": "system", "content": "You are a helpful assistant that generates Python code."},
                        {"role": "user", "content": full_prompt}
                    ],
                )
                response = response.choices[0].message.content
                code = extract_code(response)

                if code:
                    code_output, error_occurred = run_generated_code(code)
                    predicted_plan = parse_model_output(code_output) if code_output else None
                else:
                    predicted_plan = None
                    error_occurred = True

                expected_plan = parse_golden_plan(golden_plan)

                state.expected_outputs_0shot.append(expected_plan)
                state.predicted_outputs_0shot.append(predicted_plan)
                if not error_occurred:
                    state.no_error_count_0shot += 1
                    if predicted_plan == expected_plan:
                        state.correct_output_count_0shot += 1
                        correct_status = True

                timestamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                line = (
                    f"{example_id}. [{timestamp}] | PROMPT TYPE: prompt_0shot | Correct: {correct_status} | "
                    f"ANSWER: {format_itinerary_compact(predicted_plan)} | "
                    f"EXPECTED: {format_itinerary_compact(expected_plan)} | ERROR: {'Yes' if error_occurred else 'No'}"
                )
                logging.info(line)
                txt_file.write(line + "\n")

                json_output = {
                    "final_program_time": {
                        "itinerary": predicted_plan if predicted_plan else []
                    },
                    "expected_time": {
                        "itinerary": expected_plan if expected_plan else []
                    },
                    "has_error": error_occurred,
                    "raw_model_response": response,
                    "count": example_id
                }

                # Update JSON file
                with open("O3-M-25-01-31_code_meeting_results.json", "r+") as json_file:
                    file_data = json.load(json_file)
                    file_data["0shot"].append(json_output)
                    json_file.seek(0)
                    json.dump(file_data, json_file, indent=4)
                    json_file.truncate()

                # Update processed examples and save state
                state.processed_examples.add(example_id)
                state.save()

                # Clear memory
                del response, code, code_output, predicted_plan, expected_plan
                gc.collect()
                torch.cuda.empty_cache()

            except Exception as e:
                logging.error(f"Error processing prompt {example_id}: {e}")

        # Final results
        end_time = datetime.datetime.now()
        total_runtime = state.previous_time + (end_time - state.start_time).total_seconds()
        
        accuracy_0shot = (state.correct_output_count_0shot / len(state.expected_outputs_0shot)) * 100 if state.expected_outputs_0shot else 0
        no_error_accuracy_0shot = (state.correct_output_count_0shot / state.no_error_count_0shot) * 100 if state.no_error_count_0shot > 0 else 0

        accuracy_line = (
            f"\n0-shot prompts: Model guessed {state.correct_output_count_0shot} out of {len(state.expected_outputs_0shot)} correctly.\n"
            f"Accuracy: {accuracy_0shot:.2f}%\n"
            f"\n0-shot prompts with no errors: {state.correct_output_count_0shot} out of {state.no_error_count_0shot} produced correct outputs.\n"
            f"No-error accuracy: {no_error_accuracy_0shot:.2f}%\n"
            f"\nTotal time taken: {total_runtime} seconds"
        )

        txt_file.write(accuracy_line)

if __name__ == "__main__":
    # Set environment variable to reduce memory fragmentation
    os.environ["PYTORCH_CUDA_ALLOC_CONF"] = "expandable_segments:True"
    asyncio.run(main())




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
# STATE_FILE = "meeting_planning_state_openai_other.json"

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

#     with open('O3-M-25-01-31_forceJSON_text_meeting_results.txt', txt_mode) as txt_file, \
#          open('O3-M-25-01-31_forceJSON_text_meeting_results.json', json_mode) as json_file:
        
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


