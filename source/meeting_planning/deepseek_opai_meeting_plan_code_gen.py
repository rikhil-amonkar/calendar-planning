#**********WORKING CODE, CODE GENERATION, MEETING PLANNING, KANI, CHECKPOINT************

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
from openai import OpenAI

# Configure logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')

# Read the API key from a file
with open('/home/rma336/openai_research/deepseek_api_key.txt', 'r') as key_file:
    api_key = key_file.read().strip()

# Initialize the OpenAI client
deepseek_client = OpenAI(api_key=api_key, base_url="https://api.deepseek.com")

# Argument parser to select the model
parser = argparse.ArgumentParser(description="Select a HuggingFace model.")
parser.add_argument('--model', type=str, required=True, help="The HuggingFace model ID to use.")
args = parser.parse_args()

# State management
STATE_FILE = "meeting_planning_state_deepseek_code.json"

class EvaluationState:
    def __init__(self):
        self.expected_outputs_0shot = []
        self.predicted_outputs_0shot = []
        # self.expected_outputs_5shot = []
        # self.predicted_outputs_5shot = []
        self.start_time = datetime.datetime.now()
        self.no_error_count_0shot = 0
        self.correct_output_count_0shot = 0
        # self.no_error_count_5shot = 0
        # self.correct_output_count_5shot = 0
        self.processed_examples = set()
        self.previous_time = 0
        self.first_run = True

    def save(self):
        state_to_save = {
            "expected_outputs_0shot": self.expected_outputs_0shot,
            "predicted_outputs_0shot": self.predicted_outputs_0shot,
            # "expected_outputs_5shot": self.expected_outputs_5shot,
            # "predicted_outputs_5shot": self.predicted_outputs_5shot,
            "start_time": self.start_time.isoformat(),
            "no_error_count_0shot": self.no_error_count_0shot,
            "correct_output_count_0shot": self.correct_output_count_0shot,
            # "no_error_count_5shot": self.no_error_count_5shot,
            # "correct_output_count_5shot": self.correct_output_count_5shot,
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
                # self.expected_outputs_5shot = loaded["expected_outputs_5shot"]
                # self.predicted_outputs_5shot = loaded["predicted_outputs_5shot"]
                self.no_error_count_0shot = loaded["no_error_count_0shot"]
                self.correct_output_count_0shot = loaded["correct_output_count_0shot"]
                # self.no_error_count_5shot = loaded["no_error_count_5shot"]
                # self.correct_output_count_5shot = loaded["correct_output_count_5shot"]
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
    '  "schedule": [\n'
    '    {"action": "start", "location": "Location Name", "time": "H:MMAM/PM"},\n'
    '    {"action": "travel", "location": "Destination", "duration": X, "time": "H:MMAM/PM", "to": "Destination"},\n'
    '    {"action": "wait", "location": "Location Name", "time": "H:MMAM/PM"},\n'
    '    {"action": "meet", "location": "Location Name", "duration": X, "time": "H:MMAM/PM"}\n'
    "  ]\n"
    "}\n"
    "Rules for the program:\n"
    "- Times should be in format like '9:00AM' (no leading zero) and durations in minutes\n"
    "- The schedule must account for all travel times and constraints\n"
    "- The program must actually compute the schedule, not just print a static answer\n"
    "\n"
    "Output only the complete Python code with no additional text or explanation.\n"
    "The code must run independently and output valid JSON when executed."
)

def initialize_engine(model_id):
    try:
        # Check for OpenAI models (both gpt-* and o3-* prefixes)
        if model_id.startswith("gpt-") or model_id.startswith("o3-"):
            # For OpenAI models, we'll use the client directly in the chat function
            return None
        elif model_id.startswith("deepseek-"):
            # For DeepSeek models, we'll use the DeepSeek client directly
            return None
        else:
            # For HuggingFace models
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

async def chat_with_model(ai, full_prompt, model_id):
    if model_id.startswith("gpt-"):
        # Use OpenAI API
        response = openai_client.chat.completions.create(
            model=model_id,
            messages=[
                {"role": "system", "content": "You are a helpful assistant that generates Python code."},
                {"role": "user", "content": full_prompt}
            ],
        )
        return response.choices[0].message.content
    elif model_id.startswith("deepseek-"):
        # Use DeepSeek API
        response = deepseek_client.chat.completions.create(
            model="deepseek-chat",
            messages=[
                {"role": "system", "content": "You are a helpful assistant that generates Python code."},
                {"role": "user", "content": full_prompt}
            ],
            stream=False
        )
        return response.choices[0].message.content
    else:
        # Use Kani with HuggingFace
        response = await ai.chat_round_str(full_prompt)
        # Stop the response after the second '''
        return stop_after_second_triple_quote(response)

# Function to extract the code from the model's response
def extract_code(response):
    """Extract Python code from a response, completely removing any markdown delimiters."""
    response = response.strip()
    
    # Handle markdown code blocks (```python or ```)
    if response.startswith("```python"):
        end = response.find("```", 9)
        if end != -1:
            return response[9:end].strip()
    elif response.startswith("```"):
        end = response.find("```", 3)
        if end != -1:
            return response[3:end].strip()
    
    # Handle other cases (existing logic)
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

def stop_after_second_triple_quote(response):
    """Stop after second triple quote and remove both sets of quotes."""
    first_triple = response.find("```")
    if first_triple == -1:
        return response
    
    second_triple = response.find("```", first_triple + 3)
    if second_triple == -1:
        return response
    
    # Extract content between the triple quotes
    content = response[first_triple+3:second_triple].strip()
    
    # Remove any remaining python label if present
    if content.startswith("python\n"):
        content = content[7:]
    
    return content

def categorize_error(error_message):
    error_types = ["SyntaxError", "IndentationError", "NameError", "TypeError", "ValueError", "ImportError", "RuntimeError", "AttributeError", "KeyError", "IndexError"]
    for error_type in error_types:
        if error_type in error_message:
            return error_type
    return "Other"

def run_generated_code(code):
    try:
        with open("generated_code_deepseek_code.py", "w") as file:
            file.write(code)
        result = subprocess.run(["python", "generated_code_deepseek_code.py"], capture_output=True, text=True, check=True)
        output = result.stdout.strip()
        return output, None
    except subprocess.CalledProcessError as e:
        error_type = categorize_error(e.stderr)
        return None, error_type

def remove_leading_zero_from_time(time_str):
    """Remove leading zero from the time string if the hour is a single digit."""
    if not time_str:
        return time_str
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

def parse_model_output(model_output):
    """Parse the model's JSON output into structured schedule format, handling SOLUTION: cases."""
    if not model_output:
        return None
    
    # Handle SOLUTION: prefix case
    if isinstance(model_output, str) and model_output.startswith("SOLUTION:"):
        model_output = model_output[len("SOLUTION:"):].strip()
    
    try:
        # First try to parse the output directly as JSON (in case it's just the JSON)
        try:
            if isinstance(model_output, str):
                schedule_data = json.loads(model_output)
            else:
                schedule_data = model_output
            return normalize_schedule(schedule_data)
        except json.JSONDecodeError:
            pass
        
        # If direct JSON parsing fails, look for JSON in print output
        json_pattern = r'\{.*?"schedule"\s*:\s*\[.*?\]\}'
        matches = re.search(json_pattern, model_output, re.DOTALL)
        if matches:
            try:
                schedule_data = json.loads(matches.group(0))
                return normalize_schedule(schedule_data)
            except json.JSONDecodeError:
                pass
        
        # If we still haven't found JSON, try to find the last dictionary-looking structure
        dict_pattern = r'\{[\s\S]*?\}'
        matches = re.findall(dict_pattern, model_output)
        if matches:
            # Try each match from last to first (most likely the output is at the end)
            for match in reversed(matches):
                try:
                    schedule_data = json.loads(match)
                    if "schedule" in schedule_data:
                        return normalize_schedule(schedule_data)
                except json.JSONDecodeError:
                    continue
        
        return None
        
    except Exception as e:
        logging.error(f"Error parsing model output: {e}")
        return None

def normalize_schedule(schedule_data):
    """Normalize the schedule data into our standard format."""
    if not isinstance(schedule_data, dict) or "schedule" not in schedule_data:
        return None
    
    schedule = schedule_data.get("schedule", [])
    normalized_schedule = []
    last_time = None
    
    for step in schedule:
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
        
        normalized_schedule.append(cleaned_step)
    
    return normalized_schedule

def stop_after_second_triple_quote(response):
    first_triple_quote = response.find("'''")
    if first_triple_quote == -1:
        return response  # No triple quotes found
    second_triple_quote = response.find("'''", first_triple_quote + 3)
    if second_triple_quote == -1:
        return response  # Only one triple quote found
    return response[:second_triple_quote + 3]  # Stop after the second triple quote

def format_schedule_compact(schedule):
    """Convert schedule to compact string representation for display."""
    if not schedule:
        return "None"
    
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
    # Initialize the model engine
    engine = initialize_engine(args.model)
    ai = Kani(engine) if engine else None  # Only create Kani instance for HuggingFace models

    # Initialize state
    state = EvaluationState()
    state_loaded = state.load()

    # Determine file open mode
    txt_mode = 'a' if state_loaded and not state.first_run else 'w'

    # Ensure the JSON file exists with the correct structure
    if not os.path.exists("DS-R1-FULL_code_meeting_results.json") or not state_loaded:
        with open("DS-R1-FULL_code_meeting_results.json", "w") as json_file:
            json.dump({"0shot": []}, json_file, indent=4)

    with open("DS-R1-FULL_code_meeting_results.txt", txt_mode) as txt_file:
        # Write header if this is a fresh run
        if not state_loaded or state.first_run:
            with open("DS-R1-FULL_code_meeting_results.json", "w") as json_file:
                json.dump({"0shot": []}, json_file, indent=4)
            state.first_run = False

        for example_id, example in meeting_examples.items():
            # Skip already processed examples
            if example_id in state.processed_examples:
                continue
                
            for prompt_type in ["prompt_0shot"]:
                if prompt_type not in example:
                    continue
                    
                prompt = example[prompt_type]
                golden_plan = example["golden_plan"]
                full_prompt = prefix_message + prompt + suffix_message
                correct_status = False

                try:
                    # Get response from appropriate API
                    if args.model.startswith("gpt-"):
                        response = openai_client.chat.completions.create(
                            model=args.model,
                            messages=[
                                {"role": "system", "content": "You are a helpful assistant that generates Python code."},
                                {"role": "user", "content": full_prompt}
                            ],
                        )
                        response = response.choices[0].message.content
                    elif args.model.startswith("deepseek-"):
                        response = deepseek_client.chat.completions.create(
                            model="deepseek-chat",
                            messages=[
                                {"role": "system", "content": "You are a helpful assistant that generates Python code."},
                                {"role": "user", "content": full_prompt}
                            ],
                            stream=False
                        )
                        response = response.choices[0].message.content
                    else:
                        response = await ai.chat_round_str(full_prompt)
                        response = stop_after_second_triple_quote(response)

                    code = extract_code(response)

                    if code:
                        code_output, error_type = run_generated_code(code)
                        predicted_plan = parse_model_output(code_output) if code_output else None
                    else:
                        predicted_plan = None
                        error_type = "NoCodeGenerated"

                    expected_plan = parse_golden_plan(golden_plan)

                    if prompt_type == "prompt_0shot":
                        state.expected_outputs_0shot.append(expected_plan)
                        state.predicted_outputs_0shot.append(predicted_plan)
                        if error_type is None:
                            state.no_error_count_0shot += 1
                            if predicted_plan == expected_plan:
                                state.correct_output_count_0shot += 1
                                correct_status = True
                    # elif prompt_type == "prompt_5shot":
                    #     state.expected_outputs_5shot.append(expected_plan)
                    #     state.predicted_outputs_5shot.append(predicted_plan)
                    #     if error_type is None:
                    #         state.no_error_count_5shot += 1
                    #         if predicted_plan == expected_plan:
                    #             state.correct_output_count_5shot += 1
                    #             correct_status = True

                    timestamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                    line = (
                        f"{example_id}. [{timestamp}] | PROMPT TYPE: {prompt_type} | Correct: {correct_status} | "
                        f"ANSWER: {format_schedule_compact(predicted_plan)} | "
                        f"EXPECTED: {format_schedule_compact(expected_plan)} | ERROR: {error_type}"
                    )
                    logging.info(line)
                    txt_file.write(line + "\n")

                    json_output = {
                        "final_program_plan": predicted_plan,
                        "expected_plan": expected_plan,
                        "type_error": error_type,
                        "full_response": response,
                        "count": example_id,
                        "is_correct": correct_status
                    }

                    # Update JSON file
                    with open("DS-R1-FULL_code_meeting_results.json", "r+") as json_file:
                        file_data = json.load(json_file)
                        if prompt_type == "prompt_0shot":
                            file_data["0shot"].append(json_output)
                        # elif prompt_type == "prompt_5shot":
                        #     file_data["5shot"].append(json_output)
                        json_file.seek(0)
                        json.dump(file_data, json_file, indent=4)
                        json_file.truncate()

                    # Update processed examples and save state
                    state.processed_examples.add(example_id)
                    state.save()

                    # Clear memory
                    del response, code, code_output, predicted_plan, expected_plan, error_type, json_output
                    gc.collect()
                    torch.cuda.empty_cache()

                except Exception as e:
                    logging.error(f"Error processing prompt {example_id}: {e}")

        # Final results
        end_time = datetime.datetime.now()
        total_runtime = state.previous_time + (end_time - state.start_time).total_seconds()
        
        accuracy_0shot = (state.correct_output_count_0shot / len(state.expected_outputs_0shot)) * 100 if state.expected_outputs_0shot else 0
        # accuracy_5shot = (state.correct_output_count_5shot / len(state.expected_outputs_5shot)) * 100 if state.expected_outputs_5shot else 0
        # total_accuracy = ((state.correct_output_count_0shot + state.correct_output_count_5shot) / 
                        #  (len(state.expected_outputs_0shot) + len(state.expected_outputs_5shot))) * 100 if (state.expected_outputs_0shot + state.expected_outputs_5shot) else 0

        no_error_accuracy_0shot = (state.correct_output_count_0shot / state.no_error_count_0shot) * 100 if state.no_error_count_0shot > 0 else 0
        # no_error_accuracy_5shot = (state.correct_output_count_5shot / state.no_error_count_5shot) * 100 if state.no_error_count_5shot > 0 else 0

        accuracy_line = (
            f"\n0-shot prompts: Model guessed {state.correct_output_count_0shot} out of {len(state.expected_outputs_0shot)} correctly.\n"
            f"Accuracy: {accuracy_0shot:.2f}%\n"
            # f"\n5-shot prompts: Model guessed {state.correct_output_count_5shot} out of {len(state.expected_outputs_5shot)} correctly.\n"
            # f"Accuracy: {accuracy_5shot:.2f}%\n"
            # f"\nTotal accuracy: {total_accuracy:.2f}%\n"
            f"\n0-shot prompts with no errors: {state.correct_output_count_0shot} out of {state.no_error_count_0shot} produced correct outputs.\n"
            f"No-error accuracy: {no_error_accuracy_0shot:.2f}%\n"
            # f"\n5-shot prompts with no errors: {state.correct_output_count_5shot} out of {state.no_error_count_5shot} produced correct outputs.\n"
            # f"No-error accuracy: {no_error_accuracy_5shot:.2f}%\n"
            f"\nTotal time taken: {total_runtime} seconds"
        )

        txt_file.write(accuracy_line)

if __name__ == "__main__":
    # Set environment variable to reduce memory fragmentation
    os.environ["PYTORCH_CUDA_ALLOC_CONF"] = "expandable_segments:True"
    asyncio.run(main())