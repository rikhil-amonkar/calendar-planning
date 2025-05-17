import asyncio
import json
import logging
import os
import re
import subprocess
from argparse import ArgumentParser
from datetime import datetime
from kani import Kani
from kani.engines.huggingface import HuggingEngine
import torch
import gc
import argparse
from openai import OpenAI

# Read the API key from a file
with open('/home/rma336/openai_research/openai_api_key.txt', 'r') as key_file:
    api_key = key_file.read().strip()

# Initialize the OpenAI client
client = OpenAI(api_key=api_key)

# Configure logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')

# Argument parser to select the model
parser = argparse.ArgumentParser(description="Select an OpenAI model.")
parser.add_argument('--model', type=str, required=True, help="The OpenAI model ID to use.")
args = parser.parse_args()

# State management
STATE_FILE = "code_trip_planning_state.json"

class EvaluationState:
    def __init__(self):
        self.expected_outputs_0shot = []
        self.predicted_outputs_0shot = []
        self.start_time = datetime.now()
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
                self.start_time = datetime.fromisoformat(loaded["start_time"])
                self.first_run = loaded.get("first_run", False)
            return True
        except (FileNotFoundError, json.JSONDecodeError, KeyError):
            return False

def load_prompts(file_path):
    try:
        with open(file_path, "r") as file:
            prompts = json.load(file)
            return prompts
    except Exception as e:
        logging.error(f"Error loading prompts: {e}")
        raise

prefix_message = (
    "You are an expert computational trip planner. Your task is to write a Python program that "
    "algorithmically calculates the optimal itinerary based on the participants' constraints.\n"
    "The program must actually compute the plan using the given parameters, not just print a pre-determined answer.\n"
    "Input parameters:\n"
)

suffix_message = (
    "\n\nGenerate a complete, self-contained Python program that:\n"
    "1. Takes the above trip constraints as input variables\n"
    "2. Computes the optimal itinerary using logical rules and calculations\n"
    "3. Outputs the result as a JSON-formatted dictionary containing only day ranges and places.\n"
    "4. Note that if one flies from city A to city B on day X, then they are in both cities A and B on day X, which contributes to the total number of days in each city.\n"
    "The program must include:\n"
    "- Actual calculations to determine durations in each location\n"
    "- Correct sequencing of destinations based on the constraints\n"
    "\n"
    "IMPORTANT: Only include day_range and place in the output - no flying information.\n"
    "Output only the complete Python code with no additional text or explanation.\n"
    "Encase the code in triple backticks (```python) and ensure it is valid Python code.\n"
    "The code must run independently and output valid JSON when executed."
)

def initialize_engine(model_id):
    try:
        return None
    except Exception as e:
        logging.error(f"Error initializing model: {e}")
        raise

def extract_code(response):
    """Extract Python code from a response, returning clean code without any delimiters."""
    response = response.strip()
    
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
    
    indicator_count = sum(1 for indicator in python_indicators if indicator in response)
    
    if indicator_count >= 3 and '\n' in response:
        return response.strip()
    
    delimiters = [
        ("```python", "```"),
        ("```", "```"),
        ("'''python", "'''"),
        ("'''", "'''"),
        ('"""python', '"""'),
        ('"""', '"""')
    ]
    
    for start_delim, end_delim in delimiters:
        start_idx = response.find(start_delim)
        if start_idx != -1:
            start_idx += len(start_delim)
            end_idx = response.find(end_delim, start_idx)
            if end_idx != -1:
                extracted = response[start_idx:end_idx].strip()
                if any(indicator in extracted for indicator in python_indicators):
                    return extracted
    
    lines = response.split('\n')
    if len(lines) > 1 and all(line.startswith(('    ', '\t')) for line in lines[1:] if line.strip()):
        return response
    
    if indicator_count >= 1:
        return response
    
    return None

def categorize_error(error_message):
    error_types = ["SyntaxError", "IndentationError", "NameError", "TypeError", "ValueError", "ImportError", "RuntimeError", "AttributeError", "KeyError", "IndexError"]
    for error_type in error_types:
        if error_type in error_message:
            return error_type
    return "Other"

def run_generated_code(code):
    try:
        clean_code = code.replace('```python', '').replace('```', '').replace('"""python', '').replace('"""', '').replace("'''python", "").replace("'''", "").strip()
        
        with open("generated_code_openai.py", "w") as file:
            file.write(clean_code)
        
        result = subprocess.run(["python", "generated_code_openai.py"], 
                              capture_output=True, 
                              text=True, 
                              check=True)
        output = result.stdout.strip()
        return output, None
    except subprocess.CalledProcessError as e:
        error_type = categorize_error(e.stderr)
        return None, error_type

def format_itinerary(itinerary):
    """Format itinerary items into 'Day X-Y: Place' format."""
    if not itinerary:
        return None
    
    formatted = []
    for item in itinerary:
        if isinstance(item, dict):
            # Extract day range (handle both 'Day X-Y' and 'X-Y' formats)
            day_range = item.get("day_range", "")
            if not day_range.startswith("Day "):
                day_range = f"Day {day_range}"
            
            # Clean up day range (remove any extra spaces or 'Day' duplicates)
            day_range = day_range.replace("Day Day", "Day").strip()
            
            # Get place name
            place = item.get("place", "").strip()
            
            if day_range and place:
                formatted.append(f"{day_range}: {place}")
    
    if not formatted:
        return None
    
    return ", ".join(formatted)

def parse_model_output(model_output):
    """Parse the model's JSON output into structured itinerary."""
    if not model_output:
        return None
    
    try:
        if isinstance(model_output, str):
            itinerary = json.loads(model_output)
        else:
            itinerary = model_output
        
        # First normalize to list of dicts with day_range and place
        normalized = []
        for item in itinerary:
            if isinstance(item, dict):
                entry = {}
                
                # Handle day_range (accept both 'Day X-Y' and 'X-Y' formats)
                if "day_range" in item:
                    day_range = item["day_range"]
                    if not day_range.startswith("Day "):
                        day_range = f"Day {day_range}"
                    entry["day_range"] = day_range
                elif "days" in item:  # alternative format
                    days = item["days"].split("-")
                    entry["day_range"] = f"Day {days[0]}-{days[1]}"
                
                # Handle place
                if "place" in item:
                    entry["place"] = item["place"]
                elif "location" in item:  # alternative format
                    entry["place"] = item["location"]
                
                if "day_range" in entry and "place" in entry:
                    normalized.append(entry)
        
        return format_itinerary(normalized) if normalized else None
    
    except json.JSONDecodeError:
        return None
    except Exception as e:
        logging.error(f"Error parsing model output: {e}")
        return None

def parse_golden_plan(golden_plan):
    """Parse the golden plan into structured itinerary format."""
    itinerary = []
    
    for line in golden_plan.split('\n'):
        line = line.strip()
        if not line or not line.startswith('**Day'):
            continue
            
        day_match = re.search(r'Day (\d+)(?:-(\d+))?', line)
        if not day_match:
            continue
            
        start_day = int(day_match.group(1))
        end_day = int(day_match.group(2)) if day_match.group(2) else start_day
        day_range = f"Day {start_day}-{end_day}"
        
        # Skip flying days completely
        if "Fly from" in line:
            continue
            
        # Handle regular days
        place = None
        if "Arriving in" in line:
            place = re.search(r'Arriving in ([^\s,.]+)', line).group(1)
        elif "Visit" in line:
            place = re.search(r'Visit ([^\s,.]+)', line).group(1)
        
        if place:
            itinerary.append({
                "day_range": day_range,
                "place": place
            })
    
    return format_itinerary(itinerary)

def stop_after_second_triple_quote(response):
    first_triple_quote = response.find("'''")
    if first_triple_quote == -1:
        return response
    second_triple_quote = response.find("'''", first_triple_quote + 3)
    if second_triple_quote == -1:
        return response
    return response[:second_triple_quote + 3]

async def run_model():
    state = EvaluationState()
    state_loaded = state.load()

    txt_mode = 'a' if state_loaded and not state.first_run else 'w'

    prompts_data = load_prompts("../../data/trip_planning_100.json")
    prompts_list = list(prompts_data.items())

    if not os.path.exists("O3-M-25-01-31_code_trip_results.json") or not state_loaded:
        with open("O3-M-25-01-31_code_trip_results.json", "w") as json_file:
            json.dump({"0shot": []}, json_file, indent=4)

    with open("O3-M-25-01-31_code_trip_results.txt", txt_mode) as txt_file:
        if not state_loaded or state.first_run:
            with open("O3-M-25-01-31_code_trip_results.json", "w") as json_file:
                json.dump({"0shot": []}, json_file, indent=4)
            state.first_run = False

        for key, data in prompts_list:
            if key in state.processed_examples:
                continue
                
            for prompt_type in ["prompt_0shot"]:
                if prompt_type not in data:
                    continue
                    
                prompt = data[prompt_type]
                golden_plan = data["golden_plan"]
                full_prompt = prefix_message + prompt + suffix_message
                correct_status = False

                try:
                    response = client.chat.completions.create(
                        model=args.model,
                        messages=[
                            {"role": "system", "content": "You are a helpful assistant that generates Python code for trip planning."},
                            {"role": "user", "content": full_prompt}
                        ],
                    )
                    
                    response_content = response.choices[0].message.content
                    response_content = stop_after_second_triple_quote(response_content)
                    code = extract_code(response_content)
                    
                    if code:
                        code_output, error_type = run_generated_code(code)
                        predicted_plan = parse_model_output(code_output) if code_output else None
                    else:
                        predicted_plan = None
                        error_type = "NoCodeGenerated"

                    expected_plan = parse_golden_plan(golden_plan)

                    if predicted_plan is not None and expected_plan is not None:
                        correct_status = (predicted_plan == expected_plan)

                    if prompt_type == "prompt_0shot":
                        state.expected_outputs_0shot.append(expected_plan)
                        state.predicted_outputs_0shot.append(predicted_plan)
                        if error_type is None:
                            state.no_error_count_0shot += 1
                            if correct_status:
                                state.correct_output_count_0shot += 1

                    timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                    line = (
                        f"{key}. [{timestamp}] | PROMPT TYPE: {prompt_type} | Correct: {correct_status} | ANSWER: {predicted_plan} | "
                        f"EXPECTED: {expected_plan} | ERROR: {error_type}"
                    )
                    logging.info(line)
                    txt_file.write(line + "\n")

                    json_output = {
                        "final_program_plan": predicted_plan,
                        "expected_plan": expected_plan,
                        "type_error": error_type,
                        "full_response": response_content,
                        "count": key,
                        "is_correct": correct_status
                    }

                    with open("O3-M-25-01-31_code_trip_results.json", "r+") as json_file:
                        file_data = json.load(json_file)
                        if prompt_type == "prompt_0shot":
                            file_data["0shot"].append(json_output)
                        json_file.seek(0)
                        json.dump(file_data, json_file, indent=4)
                        json_file.truncate()

                    state.processed_examples.add(key)
                    state.save()

                    del response, code, code_output, predicted_plan, expected_plan, error_type, json_output
                    gc.collect()
                    torch.cuda.empty_cache()

                except Exception as e:
                    logging.error(f"Error processing prompt {key}: {e}")

        end_time = datetime.now()
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
    os.environ["PYTORCH_CUDA_ALLOC_CONF"] = "expandable_segments:True"
    asyncio.run(run_model())