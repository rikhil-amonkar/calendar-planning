# #**********WORKING CODE, FORCE JSON, TEXT OUTPUTS, MEETING PLANNING, KANI, CHECKPOINT************

import argparse
import asyncio
import json
import datetime
import outlines
import transformers
import re
from kani import Kani
from kani.engines.huggingface import HuggingEngine
from kani.engines import WrapperEngine
import os

# Define the structured JSON schema for the meeting plan output
JSON_SCHEMA = {
    "type": "object",
    "properties": {
        "schedule": {
            "type": "array",
            "items": {
                "type": "object",
                "properties": {
                    "action": {"type": "string", "enum": ["start", "travel", "wait", "meet"]},
                    "location": {"type": "string"},
                    "time": {"type": "string"},
                    "duration": {"type": "number", "minimum": 0},
                    "to": {"type": "string"}  # only for travel actions
                },
                "required": ["action", "location"],
                "anyOf": [
                    {
                        "properties": {
                            "action": {"const": "start"}
                        },
                        "required": ["time"]
                    },
                    {
                        "properties": {
                            "action": {"const": "travel"}
                        },
                        "required": ["duration", "to"]
                    },
                    {
                        "properties": {
                            "action": {"const": "wait"}
                        },
                        "required": ["time"]
                    },
                    {
                        "properties": {
                            "action": {"const": "meet"}
                        },
                        "required": ["duration"]
                    }
                ]
            }
        }
    },
    "required": ["schedule"]
}

# Load the meeting planning examples from the JSON file
with open('100_meeting_planning_examples.json', 'r') as file:
    meeting_examples = json.load(file)

# Argument parser to select the model
parser = argparse.ArgumentParser(description="Select a HuggingFace model.")
parser.add_argument('--model', type=str, required=True, help="The HuggingFace model ID to use.")
args = parser.parse_args()

# State management
STATE_FILE = "meeting_planning_state.json"

class JSONGuidanceHFWrapper(WrapperEngine):
    def __init__(self, engine: HuggingEngine, *args, json_schema, **kwargs):
        super().__init__(engine, *args, **kwargs)
        self.engine: HuggingEngine  # type hint for IDEs
        self.json_schema = json_schema
        self.outlines_tokenizer = outlines.models.TransformerTokenizer(self.engine.tokenizer)

    def _create_logits_processor(self):
        json_logits_processor = outlines.processors.JSONLogitsProcessor(self.json_schema, self.outlines_tokenizer)
        return transformers.LogitsProcessorList([json_logits_processor])

    async def predict(self, *args, **kwargs):
        if "logits_processor" not in kwargs:
            kwargs["logits_processor"] = self._create_logits_processor()
        return await super().predict(*args, **kwargs)

    async def stream(self, *args, **kwargs):
        if "logits_processor" not in kwargs:
            kwargs["logits_processor"] = self._create_logits_processor()
        async for elem in super().stream(*args, **kwargs):
            yield elem

class EvaluationState:
    def __init__(self):
        self.correct_0shot = 0
        self.correct_5shot = 0
        self.total_0shot = 0
        self.total_5shot = 0
        self.results_0shot = []
        self.results_5shot = []
        self.processed_examples = set()
        self.start_time = datetime.datetime.now()
        self.previous_time = datetime.timedelta(0)
        self.first_run = True

    def save(self):
        state_to_save = {
            "correct_0shot": self.correct_0shot,
            "correct_5shot": self.correct_5shot,
            "total_0shot": self.total_0shot,
            "total_5shot": self.total_5shot,
            "results_0shot": self.results_0shot,
            "results_5shot": self.results_5shot,
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
                self.correct_5shot = loaded["correct_5shot"]
                self.total_0shot = loaded["total_0shot"]
                self.total_5shot = loaded["total_5shot"]
                self.results_0shot = loaded["results_0shot"]
                self.results_5shot = loaded["results_5shot"]
                self.processed_examples = set(loaded["processed_examples"])
                self.previous_time = datetime.timedelta(seconds=loaded["previous_time"])
                self.start_time = datetime.datetime.fromisoformat(loaded["start_time"])
                self.first_run = loaded.get("first_run", False)
            return True
        except (FileNotFoundError, json.JSONDecodeError, KeyError):
            return False

def remove_leading_zero_from_time(time_str):
    """Remove leading zero from the time string if the hour is a single digit."""
    # Handle both "HH:MMAM/PM" and "HH:MM AM/PM" formats
    time_str = time_str.replace(" ", "")
    time_part, period = time_str[:-2], time_str[-2:].upper()
    
    time_parts = time_part.split(":")
    if len(time_parts[0]) == 2 and time_parts[0][0] == "0":
        time_parts[0] = time_parts[0][1]  # Remove leading zero
    
    return f"{':'.join(time_parts)}{period}"

def parse_golden_plan(golden_plan):
    """Parse the golden plan into structured schedule format matching our JSON schema."""
    schedule = []
    last_time = None  # Track the last time encountered
    
    for step in golden_plan:
        step = step.strip()
        if not step:
            continue
            
        # Parse start action
        if step.startswith("You start at"):
            match = re.search(r"You start at (.+?) at (.+?)\.", step)
            if match:
                time = remove_leading_zero_from_time(match.group(2))
                schedule.append({
                    "action": "start",
                    "location": match.group(1),
                    "time": time
                })
                last_time = time
                
        # Parse travel action
        elif "travel to" in step:
            match = re.search(r"You travel to (.+?) in (\d+) minutes and arrive at (.+?)\.", step)
            if match:
                time = remove_leading_zero_from_time(match.group(3))
                schedule.append({
                    "action": "travel",
                    "location": match.group(1),
                    "duration": int(match.group(2)),
                    "time": time,
                    "to": match.group(1)
                })
                last_time = time
                
        # Parse wait action
        elif "wait until" in step:
            match = re.search(r"You wait until (.+?)\.", step)
            if match:
                time = remove_leading_zero_from_time(match.group(1))
                schedule.append({
                    "action": "wait",
                    "location": schedule[-1]["location"] if schedule else "Unknown",
                    "time": time
                })
                last_time = time
                
        # Parse meet action
        elif "meet" in step and "for" in step:
            match = re.search(r"You meet (.+?) for (\d+) minutes from (.+?) to (.+?)\.", step)
            if match:
                time = remove_leading_zero_from_time(match.group(3))
                schedule.append({
                    "action": "meet",
                    "location": schedule[-1]["location"] if schedule else "Unknown",
                    "duration": int(match.group(2)),
                    "time": time
                })
                last_time = time
                
    return schedule

def compare_schedules(model_schedule, golden_schedule):
    """Compare two schedules and return True if they match exactly."""
    if len(model_schedule) != len(golden_schedule):
        return False
    
    for model_step, golden_step in zip(model_schedule, golden_schedule):
        # Skip if either step is not a dictionary
        if not isinstance(model_step, dict) or not isinstance(golden_step, dict):
            return False
            
        # Check action type matches
        if model_step.get("action") != golden_step.get("action"):
            return False
            
        # Check common fields
        if model_step.get("location") != golden_step.get("location"):
            return False
            
        # Action-specific checks with time normalization
        if model_step.get("action") == "travel":
            if (model_step.get("duration") != golden_step.get("duration")):
                return False
            # Only compare time if both have it
            if 'time' in model_step and 'time' in golden_step:
                if remove_leading_zero_from_time(model_step['time']) != remove_leading_zero_from_time(golden_step['time']):
                    return False
        elif model_step.get("action") == "meet":
            if (model_step.get("duration") != golden_step.get("duration")):
                return False
            # Only compare time if both have it
            if 'time' in model_step and 'time' in golden_step:
                if remove_leading_zero_from_time(model_step['time']) != remove_leading_zero_from_time(golden_step['time']):
                    return False
        elif model_step.get("action") in ["start", "wait"]:
            # Only compare time if both have it
            if 'time' in model_step and 'time' in golden_step:
                if remove_leading_zero_from_time(model_step['time']) != remove_leading_zero_from_time(golden_step['time']):
                    return False
    
    return True

def format_schedule_compact(schedule):
    """Convert schedule to compact string representation for display."""
    parts = []
    last_time = None
    
    for step in schedule:
        if not isinstance(step, dict):
            continue
            
        action = step.get("action")
        location = step.get("location", "Unknown")
        
        if action == "start":
            time = remove_leading_zero_from_time(step.get('time', '')) if 'time' in step else 'Unknown'
            parts.append(f"Start at {location} at {time}")
            last_time = time if 'time' in step else last_time
        elif action == "travel":
            duration = step.get('duration', '?')
            time = remove_leading_zero_from_time(step.get('time', '')) if 'time' in step else 'Unknown'
            parts.append(f"Travel to {location} ({duration}min)")
            last_time = time if 'time' in step else last_time
        elif action == "wait":
            time = remove_leading_zero_from_time(step.get('time', '')) if 'time' in step else 'Unknown'
            parts.append(f"Wait until {time}")
            last_time = time if 'time' in step else last_time
        elif action == "meet":
            duration = step.get('duration', '?')
            meet_time = remove_leading_zero_from_time(step.get('time', last_time if last_time else ''))
            parts.append(f"Meet for {duration}min at {meet_time}")
            last_time = meet_time
    
    return " → ".join(parts)

async def main():
    # Initialize the Kani AI with the selected model
    model = HuggingEngine(model_id=args.model)
    engine = JSONGuidanceHFWrapper(model, json_schema=JSON_SCHEMA)
    ai = Kani(engine)

    # Initialize state
    state = EvaluationState()
    state_loaded = state.load()

    # Determine file open mode
    txt_mode = 'a' if state_loaded and not state.first_run else 'w'
    json_mode = 'a' if state_loaded and not state.first_run else 'w'

    with open('DS-R1-DL-70B_forceJSON_text_meeting_results.txt', txt_mode) as txt_file, \
         open('DS-R1-DL-70B_forceJSON_text_meeting_results.json', json_mode) as json_file:
        
        # Write header if this is a fresh run
        if not state_loaded or state.first_run:
            txt_file.write("=== New Run Started ===\n")
            json_file.write("")  # Will be properly initialized later
            state.first_run = False

        for example_id, example in meeting_examples.items():
            # Skip already processed examples
            if example_id in state.processed_examples:
                continue
                
            for prompt_type in ['prompt_0shot', 'prompt_5shot']:
                prompt = example[prompt_type]
                golden_plan = example['golden_plan']

                # Parse golden plan into structured format
                golden_schedule = parse_golden_plan(golden_plan)

                # Modify prompt to request structured JSON output
                structured_prompt = (
                    "You are an AI meeting planner and your task is to schedule meetings efficiently. "
                    "Consider travel times and constraints carefully to optimize the schedule. "
                    f"{prompt}\n\nPlease provide your meeting plan in the following exact JSON format:\n"
                    "{\n"
                    '  "schedule": [\n'
                    '    {"action": "start", "location": "Location Name", "time": "H:MMAM/PM"},\n'
                    '    {"action": "travel", "location": "Destination", "duration": X, "time": "H:MMAM/PM", "to": "Destination"},\n'
                    '    {"action": "wait", "location": "Location Name", "time": "H:MMAM/PM"},\n'
                    '    {"action": "meet", "location": "Location Name", "duration": X, "time": "H:MMAM/PM"}\n'
                    "  ]\n"
                    "}\n"
                    "Note: Times should be in format like '9:00AM' (no leading zero) and durations in minutes."
                )

                # Run the model
                async def get_model_response():
                    full_response = ""
                    async for token in ai.chat_round_stream(structured_prompt):
                        full_response += token
                        print(token, end="", flush=True)
                    print()
                    return full_response.strip()
                
                try:
                    model_response = await get_model_response()
                    
                    # Clean the response to ensure valid JSON
                    model_response = model_response.strip()
                    if not model_response.startswith('{'):
                        # Try to find the first { if the response has preamble
                        start_idx = model_response.find('{')
                        if start_idx >= 0:
                            model_response = model_response[start_idx:]
                    
                    try:
                        model_data = json.loads(model_response)
                        model_schedule = model_data.get("schedule", [])
                        
                        # Validate and clean each step in the schedule
                        cleaned_schedule = []
                        last_time = None
                        for step in model_schedule:
                            if not isinstance(step, dict):
                                continue
                                
                            # Normalize action and location
                            action = step.get("action", "").lower()
                            location = step.get("location", "Unknown")
                            
                            # Handle time formatting
                            time = step.get("time")
                            if time:
                                try:
                                    time = remove_leading_zero_from_time(time)
                                except:
                                    time = None
                            
                            # Create cleaned step
                            cleaned_step = {"action": action, "location": location}
                            if time:
                                cleaned_step["time"] = time
                                last_time = time
                            
                            # Add action-specific fields
                            if action == "travel":
                                cleaned_step["duration"] = step.get("duration", 0)
                                cleaned_step["to"] = step.get("to", location)
                                if "time" in step:
                                    last_time = time
                            elif action == "meet":
                                cleaned_step["duration"] = step.get("duration", 0)
                                if "time" not in cleaned_step and last_time:
                                    cleaned_step["time"] = last_time
                            
                            cleaned_schedule.append(cleaned_step)
                        
                        model_schedule = cleaned_schedule
                        
                    except json.JSONDecodeError as e:
                        print(f"JSON decode error: {e}")
                        model_schedule = []
                        
                except Exception as e:
                    print(f"Error getting model response: {e}")
                    model_schedule = []

                # Compare with golden schedule
                is_correct = compare_schedules(model_schedule, golden_schedule)

                # Update state
                if prompt_type == 'prompt_0shot':
                    state.total_0shot += 1
                    if is_correct:
                        state.correct_0shot += 1
                else:
                    state.total_5shot += 1
                    if is_correct:
                        state.correct_5shot += 1

                # Prepare result entry
                result_entry = {
                    "example_id": example_id,
                    "prompt_type": prompt_type,
                    "model_response": model_response,
                    "model_schedule": model_schedule,
                    "golden_schedule": golden_schedule,
                    "is_correct": is_correct,
                    "timestamp": datetime.datetime.now().isoformat()
                }

                # Store results
                if prompt_type == 'prompt_0shot':
                    state.results_0shot.append(result_entry)
                else:
                    state.results_5shot.append(result_entry)

                # Format for display
                model_display = format_schedule_compact(model_schedule)
                golden_display = format_schedule_compact(golden_schedule)
                
                # Log output
                timestamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                output_line = (
                    f"{example_id}. [{timestamp}] | {prompt_type} | Correct: {is_correct} | "
                    f"ANSWER: {model_display} | EXPECTED: {golden_display}"
                )
                print(output_line)
                txt_file.write(f"{output_line}\n")

                # Save state after each prompt type
                state.processed_examples.add(example_id)
                state.save()

        # Final results handling
        current_time = datetime.datetime.now()
        total_runtime = state.previous_time + (current_time - state.start_time)
        
        # Save final JSON results
        final_results = {
            "model": args.model,
            "start_time": state.start_time.isoformat(),
            "end_time": current_time.isoformat(),
            "total_runtime_seconds": total_runtime.total_seconds(),
            "results": {
                "0shot": state.results_0shot,
                "5shot": state.results_5shot
            },
            "accuracy": {
                "0shot": state.correct_0shot / state.total_0shot if state.total_0shot > 0 else 0,
                "5shot": state.correct_5shot / state.total_5shot if state.total_5shot > 0 else 0,
                "total": (state.correct_0shot + state.correct_5shot) / (state.total_0shot + state.total_5shot) if (state.total_0shot + state.total_5shot) > 0 else 0
            }
        }
        json.dump(final_results, json_file, indent=4)

        # Final accuracy report
        txt_file.write("\n=== Final Results ===\n")
        txt_file.write(f"Model: {args.model}\n")
        txt_file.write(f"Start time: {state.start_time}\n")
        txt_file.write(f"End time: {current_time}\n")
        txt_file.write(f"Total runtime: {total_runtime}\n")
        txt_file.write(f"0-shot accuracy: {state.correct_0shot}/{state.total_0shot} ({state.correct_0shot/state.total_0shot:.2%})\n")
        txt_file.write(f"5-shot accuracy: {state.correct_5shot}/{state.total_5shot} ({state.correct_5shot/state.total_5shot:.2%})\n")
        txt_file.write(f"Total accuracy: {state.correct_0shot + state.correct_5shot}/{state.total_0shot + state.total_5shot} ({(state.correct_0shot + state.correct_5shot)/(state.total_0shot + state.total_5shot):.2%})\n")

    print("Processing complete. Results saved.")

if __name__ == "__main__":
    asyncio.run(main())

