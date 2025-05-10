# #**********WORKING CODE, CODE GENERATION, MEETING PLANNING, KANI, CHECKPOINT************

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
from kani import Kani
from kani.engines.huggingface import HuggingEngine

# Configure logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')

# Argument parser to select the model
parser = argparse.ArgumentParser(description="Select a HuggingFace model.")
parser.add_argument('--model', type=str, required=True, help="The HuggingFace model ID to use.")
args = parser.parse_args()

# State management
STATE_FILE = "meeting_planning_state_code_help.json"

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

def initialize_engine(model_id):
    try:
        engine = HuggingEngine(
            model_id=model_id
            # top_p=0.1,  # Use top-p (nucleus) sampling
            # temperature=0.2,  # Adjust temperature
            # do_sample=True,  # Enable sampling
            # repetition_penalty=1.4,  # Reduce repetition
            # max_new_tokens=3000,  # Limit the number of tokens generated
            # top_k=50,  # Limit sampling to top 50 tokens
            # num_beams=2, # Limit beam search
        )
        return engine
    except Exception as e:
        logging.error(f"Error initializing model: {e}")
        raise

def extract_code(response):
    """Extract Python code from a response, completely removing any non-code content."""
    if not response:
        return None
        
    response = response.strip()
    
    # Remove SOLUTION: prefix if present
    if response.startswith("SOLUTION:"):
        response = response[len("SOLUTION:"):].strip()
    
    # Handle markdown code blocks (```python or ```)
    code_block_start = response.find("```python")
    if code_block_start != -1:
        code_block_start += len("```python")
        code_block_end = response.find("```", code_block_start)
        if code_block_end != -1:
            return response[code_block_start:code_block_end].strip()
    
    # Handle generic code blocks (```)
    code_block_start = response.find("```")
    if code_block_start != -1:
        code_block_start += len("```")
        code_block_end = response.find("```", code_block_start)
        if code_block_end != -1:
            return response[code_block_start:code_block_end].strip()
    
    # If we get here, look for the first line that looks like Python code
    lines = response.split('\n')
    python_lines = []
    in_code = False
    
    python_keywords = [
        'import ', 'from ', 'def ', 'class ', 'return ', ' = ', 'if ', 'for ', 
        'while ', 'try:', 'except:', 'with ', 'print(', 'yield ', 'async '
    ]
    
    for line in lines:
        line = line.strip()
        if any(keyword in line for keyword in python_keywords):
            in_code = True
        if in_code:
            python_lines.append(line)
    
    if python_lines:
        return '\n'.join(python_lines)
    
    return None

def categorize_error(error_message):
    error_types = ["SyntaxError", "IndentationError", "NameError", "TypeError", "ValueError", "ImportError", "RuntimeError", "AttributeError", "KeyError", "IndexError"]
    for error_type in error_types:
        if error_type in error_message:
            return error_type
    return "Other"

def run_generated_code(code):
    try:
        with open("generated_code_meeting_code_help.py", "w") as file:
            file.write(code)
        result = subprocess.run(["python", "generated_code_meeting_code_help.py"], capture_output=True, text=True, check=True)
        output = result.stdout.strip()
        return output, None  # No error occurred
    except subprocess.CalledProcessError as e:
        error_type = categorize_error(e.stderr)
        return None, error_type  # Error occurred

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
    # Initialize the model engine
    engine = initialize_engine(args.model)
    ai = Kani(engine)

    # Initialize state
    state = EvaluationState()
    state_loaded = state.load()

    # Determine file open mode
    txt_mode = 'a' if state_loaded and not state.first_run else 'w'

    # Ensure the JSON file exists with the correct structure
    if not os.path.exists("DS-R1-DL-8B_code_meeting_results.json") or not state_loaded:
        with open("DS-R1-DL-8B_code_meeting_results.json", "w") as json_file:
            json.dump({"0shot": []}, json_file, indent=4)

    with open("DS-R1-DL-8B_code_meeting_results.txt", txt_mode) as txt_file:
        # Write header if this is a fresh run
        if not state_loaded or state.first_run:
            with open("DS-R1-DL-8B_code_meeting_results.json", "w") as json_file:
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
                response = await ai.chat_round_str(full_prompt)
                code = extract_code(response)

                if code:
                    code_output, error_type = run_generated_code(code)
                    predicted_plan = parse_model_output(code_output) if code_output else None
                else:
                    predicted_plan = None
                    error_type = "NoCodeGenerated"

                expected_plan = parse_golden_plan(golden_plan)

                state.expected_outputs_0shot.append(expected_plan)
                state.predicted_outputs_0shot.append(predicted_plan)
                if error_type is None:
                    state.no_error_count_0shot += 1
                    if predicted_plan == expected_plan:
                        state.correct_output_count_0shot += 1
                        correct_status = True

                timestamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                line = (
                    f"{example_id}. [{timestamp}] | PROMPT TYPE: prompt_0shot | Correct: {correct_status} | "
                    f"ANSWER: {format_itinerary_compact(predicted_plan)} | "
                    f"EXPECTED: {format_itinerary_compact(expected_plan)} | ERROR: {'Yes' if error_type else 'No'}"
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
                    "has_error": bool(error_type),
                    "raw_model_response": response,
                    "count": example_id
                }

                # Update JSON file
                with open("DS-R1-DL-8B_code_meeting_results.json", "r+") as json_file:
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