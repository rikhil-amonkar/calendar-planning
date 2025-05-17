# #**********WORKING CODE, FORCE JSON, TEXT OUTPUTS, MEETING PLANNING, OPENAI, CHECKPOINT************

import argparse
import asyncio
import json
import datetime
import re
from openai import OpenAI

# Read the API key from a file
with open('/home/rma336/openai_research/deepseek_api_key.txt', 'r') as key_file:
    api_key = key_file.read().strip()

# Initialize the OpenAI client
client = OpenAI(api_key=api_key, base_url="https://api.deepseek.com")

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
STATE_FILE = "meeting_planning_state_deepseek.json"

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

    with open('DS-R1-FULL_forceJSON_text_meeting_results.txt', txt_mode) as txt_file, \
         open('DS-R1-FULL_forceJSON_text_meeting_results.json', json_mode) as json_file:
        
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

            # Run the model with DeepSeek API
            response = client.chat.completions.create(
                model=args.model,
                messages=[
                    {"role": "system", "content": "You are a helpful assistant that schedules meetings in a JSON format."},
                    {"role": "user", "content": structured_prompt}
                ],
                response_format={"type": "json_object"}
            )

            model_response = response.choices[0].message.content
            
            try:
                model_data = json.loads(model_response)
                
                # Handle both direct "itinerary" and "SOLUTION.itinerary" cases
                if "SOLUTION" in model_data and "itinerary" in model_data["SOLUTION"]:
                    model_itinerary = model_data["SOLUTION"]["itinerary"]
                else:
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
                "final_program_time": {"itinerary": model_itinerary if model_itinerary else None},
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
                f"ANSWER: {model_display if model_display else None} | EXPECTED: {golden_display}"
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