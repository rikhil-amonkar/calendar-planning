import argparse
import asyncio
import json
import datetime
import re
import tiktoken
from kani import Kani
from kani.engines.huggingface import HuggingEngine
import os

# Load the meeting planning examples from the JSON file
with open('../../data/meeting_planning_100.json', 'r') as file:
    meeting_examples = json.load(file)

# Argument parser to select the model
parser = argparse.ArgumentParser(description="Select a HuggingFace model.")
parser.add_argument('--model', type=str, required=True, help="The HuggingFace model ID to use.")
args = parser.parse_args()

# State management
STATE_FILE = "meeting_planning_state_meeting_text.json"

class EvaluationState:
    def __init__(self):
        self.results_0shot = []
        self.processed_examples = set()
        self.start_time = datetime.datetime.now()
        self.previous_time = datetime.timedelta(0)
        self.first_run = True
        self.total_reasoning_tokens = 0

    def save(self):
        state_to_save = {
            "results_0shot": self.results_0shot,
            "processed_examples": list(self.processed_examples),
            "start_time": self.start_time.isoformat(),
            "previous_time": self.previous_time.total_seconds(),
            "first_run": self.first_run,
            "total_reasoning_tokens": self.total_reasoning_tokens
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
                self.total_reasoning_tokens = loaded.get("total_reasoning_tokens", 0)
            return True
        except (FileNotFoundError, json.JSONDecodeError, KeyError):
            return False

def convert_to_24hour(time_str):
    """Convert time string to 24-hour format without leading zeros."""
    time_str = time_str.replace(" ", "").upper()
    
    if 'AM' not in time_str and 'PM' not in time_str:
        try:
            hours, minutes = map(int, time_str.split(':'))
            if hours < 0 or hours > 23 or minutes < 0 or minutes > 59:
                return None
            return f"{hours}:{minutes:02d}"
        except:
            return None
    
    time_part = time_str[:-2]
    period = time_str[-2:]
    
    try:
        if ':' in time_part:
            hours, minutes = map(int, time_part.split(':'))
        else:
            hours = int(time_part)
            minutes = 0
    except:
        return None
    
    if hours < 0 or hours > 12 or minutes < 0 or minutes > 59:
        return None
    
    if period == "PM" and hours != 12:
        hours += 12
    elif period == "AM" and hours == 12:
        hours = 0
    
    return f"{hours}:{minutes:02d}"

def parse_golden_plan(golden_plan):
    """Parse the golden plan into structured itinerary format."""
    itinerary = []
    current_location = None
    
    for step in golden_plan:
        step = step.strip()
        if not step:
            continue
            
        if step.startswith("You start at"):
            match = re.search(r"You start at (.+?) at (.+?)\.", step)
            if match:
                current_location = match.group(1)
                start_time = convert_to_24hour(match.group(2))
                
        elif "travel to" in step:
            match = re.search(r"You travel to (.+?) in (\d+) minutes and arrive at (.+?)\.", step)
            if match:
                current_location = match.group(1)
                arrival_time = convert_to_24hour(match.group(3))
                
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
        if not isinstance(model_meet, dict) or not isinstance(golden_meet, dict):
            return False
            
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

def extract_reasoning(response):
    """Attempt to extract the reasoning portion from the model's response."""
    # Try to find text before the JSON output
    json_match = re.search(r'\{.*\}', response, re.DOTALL)
    if json_match:
        reasoning = response[:json_match.start()].strip()
    else:
        reasoning = response.strip()
    return reasoning if reasoning else "No reasoning provided"

def count_tokens(text):
    """Count tokens using tiktoken."""
    try:
        encoding = tiktoken.encoding_for_model("gpt-4")
    except ValueError:
        encoding = tiktoken.get_encoding("cl100k_base")
    tokens = encoding.encode(text)
    return len(tokens)

def extract_json_response(response):
    """Extract JSON from response, handling both direct JSON and SOLUTION wrapper cases."""
    try:
        # First try to parse the entire response as JSON
        data = json.loads(response)
        
        # Check if it's wrapped in a SOLUTION object
        if isinstance(data, dict) and "SOLUTION" in data and "itinerary" in data["SOLUTION"]:
            return data["SOLUTION"]["itinerary"]
        elif isinstance(data, dict) and "itinerary" in data:
            return data["itinerary"]
        return []
    except json.JSONDecodeError:
        # If full response isn't JSON, try to find JSON portion
        json_match = re.search(r'\{.*\}', response, re.DOTALL)
        if json_match:
            try:
                data = json.loads(json_match.group(0))
                if isinstance(data, dict) and "SOLUTION" in data and "itinerary" in data["SOLUTION"]:
                    return data["SOLUTION"]["itinerary"]
                elif isinstance(data, dict) and "itinerary" in data:
                    return data["itinerary"]
                return []
            except json.JSONDecodeError:
                return []
    return []

async def main():
    # Initialize the Kani AI with the selected model
    ai = Kani(HuggingEngine(model_id=args.model))

    # Initialize state
    state = EvaluationState()
    state_loaded = state.load()

    # Determine file open mode
    txt_mode = 'a' if state_loaded and not state.first_run else 'w'
    json_mode = 'a' if state_loaded and not state.first_run else 'w'

    with open('DS-R1-70B-REASON_text_meeting_results.txt', txt_mode) as txt_file, \
         open('DS-R1-70B-REASON_text_meeting_results.json', json_mode) as json_file:
        
        if not state_loaded or state.first_run:
            json_file.write("")
            state.first_run = False

        for example_id, example in meeting_examples.items():
            if example_id in state.processed_examples:
                continue
                
            prompt = example['prompt_0shot']
            golden_plan = example['golden_plan']

            # Parse golden plan into structured format
            golden_itinerary = parse_golden_plan(golden_plan)

            # Keep the prompt exactly the same as before
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
                print(f"Model response: {model_response}")
                
                # Extract reasoning and count tokens
                model_reason = extract_reasoning(model_response)
                try:
                    token_count = count_tokens(model_reason)
                    state.total_reasoning_tokens += token_count
                    print(f"Number of Tokens for {example_id}: {token_count}")
                except Exception as e:
                    print(f"Error counting tokens: {e}")
                    token_count = 0
                
                # Extract JSON itinerary from response
                model_itinerary = extract_json_response(model_response)
                
                # Clean and validate the itinerary
                cleaned_itinerary = []
                for meeting in model_itinerary:
                    if not isinstance(meeting, dict):
                        continue
                        
                    action = meeting.get("action", "").lower()
                    if action != "meet":
                        continue
                        
                    location = meeting.get("location", "Unknown")
                    person = meeting.get("person", "Unknown")
                    
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
                is_correct = compare_itineraries(model_itinerary, golden_itinerary)

                result_entry = {
                    "final_program_time": {"itinerary": model_itinerary},
                    "expected_time": {"itinerary": golden_itinerary},
                    "count": example_id,
                    "is_correct": is_correct,
                    "reasoning_token_count": token_count,
                    "raw_model_response": model_response,
                    "raw_model_reasoning": model_reason
                }

                state.results_0shot.append(result_entry)

                model_display = format_itinerary_compact(model_itinerary)
                golden_display = format_itinerary_compact(golden_itinerary)
                
                timestamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                output_line = (
                    f"{example_id}. [{timestamp}] | Correct: {is_correct} | "
                    f"ANSWER: {model_display} | EXPECTED: {golden_display} | "
                    f"REASONING TOKENS: {token_count}"
                )
                print(output_line)
                txt_file.write(f"{output_line}\n")

                state.processed_examples.add(example_id)
                state.save()

            except Exception as e:
                print(f"Error processing example {example_id}: {e}")

        current_time = datetime.datetime.now()
        total_runtime = state.previous_time + (current_time - state.start_time)
        
        correct_count = sum(1 for result in state.results_0shot if result["is_correct"])
        total_count = len(state.results_0shot)
        accuracy = correct_count / total_count if total_count > 0 else 0

        # Calculate average tokens (fixed the division error)
        average_tokens = state.total_reasoning_tokens / total_count if total_count > 0 else 0
        
        final_results = {
            "0shot": state.results_0shot,
            "metadata": {
                "model": args.model,
                "start_time": state.start_time.isoformat(),
                "end_time": current_time.isoformat(),
                "total_runtime_seconds": total_runtime.total_seconds(),
                "accuracy": accuracy,
                "correct_count": correct_count,
                "total_count": total_count,
                "total_reasoning_tokens": state.total_reasoning_tokens,
                "average_reasoning_tokens": average_tokens
            }
        }
        json.dump(final_results, json_file, indent=4)

        txt_file.write("\n=== Final Results ===\n")
        txt_file.write(f"Model: {args.model}\n")
        txt_file.write(f"Start time: {state.start_time}\n")
        txt_file.write(f"End time: {current_time}\n")
        txt_file.write(f"Total runtime: {total_runtime}\n")
        txt_file.write(f"Accuracy: {correct_count}/{total_count} ({accuracy:.2%})\n")
        txt_file.write(f"Total reasoning tokens: {state.total_reasoning_tokens}\n")
        txt_file.write(f"Average reasoning tokens: {average_tokens:.2f}\n")

    print("Processing complete. Results saved.")

if __name__ == "__main__":
    asyncio.run(main())

