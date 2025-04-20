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
with open('/home/rma336/openai_research/deepseek_api_key.txt', 'r') as key_file:
    api_key = key_file.read().strip()

# Initialize the OpenAI client for DeepSeek
client = OpenAI(api_key=api_key, base_url="https://api.deepseek.com")

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
        self.expected_outputs_5shot = []
        self.predicted_outputs_5shot = []
        self.start_time = datetime.now()
        self.no_error_count_0shot = 0
        self.correct_output_count_0shot = 0
        self.no_error_count_5shot = 0
        self.correct_output_count_5shot = 0
        self.processed_examples = set()
        self.previous_time = 0
        self.first_run = True

    def save(self):
        state_to_save = {
            "expected_outputs_0shot": self.expected_outputs_0shot,
            "predicted_outputs_0shot": self.predicted_outputs_0shot,
            "expected_outputs_5shot": self.expected_outputs_5shot,
            "predicted_outputs_5shot": self.predicted_outputs_5shot,
            "start_time": self.start_time.isoformat(),
            "no_error_count_0shot": self.no_error_count_0shot,
            "correct_output_count_0shot": self.correct_output_count_0shot,
            "no_error_count_5shot": self.no_error_count_5shot,
            "correct_output_count_5shot": self.correct_output_count_5shot,
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
                self.expected_outputs_5shot = loaded["expected_outputs_5shot"]
                self.predicted_outputs_5shot = loaded["predicted_outputs_5shot"]
                self.no_error_count_0shot = loaded["no_error_count_0shot"]
                self.correct_output_count_0shot = loaded["correct_output_count_0shot"]
                self.no_error_count_5shot = loaded["no_error_count_5shot"]
                self.correct_output_count_5shot = loaded["correct_output_count_5shot"]
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
    "3. Outputs the result as a JSON-formatted dictionary. \n"
    "Example structure of output from running code: [{'day_range': 'Day 1-5', 'place': 'Helsinki'}, {'flying': 'Day 5-5', 'from': 'Helsinki', 'to': 'Barcelona'}, {'day_range': 'Day 5-9', 'place': 'Barcelona'}, {'flying': 'Day 9-9', 'from': 'Barcelona', 'to': 'Florence'}, {'day_range': 'Day 9-14', 'place': 'Florence'}]"
    "\n"
    "The program must include:\n"
    "- Actual calculations to determine durations and transitions\n"
    "- Proper handling of travel days between locations\n"
    "- Correct sequencing of destinations based on the constraints\n"
    "\n"
    "Output only the complete Python code with no additional text or explanation.\n"
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
    
    if indicator_count >= 3:
        if '\n' in response:
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
        
        with open("generated_code.py", "w") as file:
            file.write(clean_code)
        
        result = subprocess.run(["python", "generated_code.py"], 
                              capture_output=True, 
                              text=True, 
                              check=True)
        output = result.stdout.strip()
        return output, None
    except subprocess.CalledProcessError as e:
        error_type = categorize_error(e.stderr)
        return None, error_type

def parse_golden_plan(golden_plan):
    """Parse the golden plan into structured itinerary format matching our JSON schema."""
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
        
        if "Fly from" in line:
            fly_match = re.search(r'Fly from ([^\s,.]+) to ([^\s,.]+)', line)
            if fly_match:
                itinerary.append({
                    "flying": day_range,
                    "from": fly_match.group(1),
                    "to": fly_match.group(2)
                })
            continue
        elif "Arriving in" in line:
            place = re.search(r'Arriving in ([^\s,.]+)', line).group(1)
        elif "Visit" in line:
            place = re.search(r'Visit ([^\s,.]+)', line).group(1)
        else:
            continue
            
        itinerary.append({
            "day_range": day_range,
            "place": place
        })
    
    return itinerary

def parse_model_output(model_output):
    """Parse the model's JSON output into structured itinerary format matching our JSON schema."""
    if not model_output:
        return None
    
    try:
        if isinstance(model_output, str):
            itinerary = json.loads(model_output)
        else:
            itinerary = model_output
        
        normalized_itinerary = []
        for item in itinerary:
            if isinstance(item, dict):
                normalized_item = {}
                
                if "day_range" in item:
                    normalized_item["day_range"] = item["day_range"]
                    normalized_item["place"] = item["place"]
                
                elif "flying" in item:
                    normalized_item["flying"] = item["flying"]
                    normalized_item["from"] = item["from"]
                    normalized_item["to"] = item["to"]
                
                elif "place" in item and "days" in item:
                    days = item["days"].split("-")
                    normalized_item["day_range"] = f"Day {days[0]}-{days[1]}"
                    normalized_item["place"] = item["place"]
                
                elif "flight_day" in item:
                    normalized_item["flying"] = f"Day {item['flight_day']}-{item['flight_day']}"
                    normalized_item["from"] = item["from"]
                    normalized_item["to"] = item["to"]
                
                else:
                    continue
                
                normalized_itinerary.append(normalized_item)
        
        return normalized_itinerary
    
    except json.JSONDecodeError:
        return None
    except Exception as e:
        logging.error(f"Error parsing model output: {e}")
        return None

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

    prompts_data = load_prompts("100_trip_planning_examples.json")
    prompts_list = list(prompts_data.items())

    if not os.path.exists("DS-R1-FULL_code_trip_results.json") or not state_loaded:
        with open("DS-R1-FULL_code_trip_results.json", "w") as json_file:
            json.dump({"0shot": [], "5shot": []}, json_file, indent=4)

    with open("DS-R1-FULL_code_trip_results.txt", txt_mode) as txt_file:
        if not state_loaded or state.first_run:
            txt_file.write("=== New Run Started ===\n")
            with open("DS-R1-FULL_code_trip_results.json", "w") as json_file:
                json.dump({"0shot": [], "5shot": []}, json_file, indent=4)
            state.first_run = False

        for key, data in prompts_list:
            if key in state.processed_examples:
                continue
                
            for prompt_type in ["prompt_0shot", "prompt_5shot"]:
                if prompt_type not in data:
                    continue
                    
                prompt = data[prompt_type]
                golden_plan = data["golden_plan"]
                full_prompt = prefix_message + prompt + suffix_message
                correct_status = False

                try:
                    # Modified API call for DeepSeek
                    response = client.chat.completions.create(
                        model="deepseek-chat",  # Using DeepSeek model
                        messages=[
                            {"role": "system", "content": "You are a helpful assistant that generates Python code for trip planning."},
                            {"role": "user", "content": full_prompt}
                        ],
                        stream=False
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

                    if prompt_type == "prompt_0shot":
                        state.expected_outputs_0shot.append(expected_plan)
                        state.predicted_outputs_0shot.append(predicted_plan)
                        if error_type is None:
                            state.no_error_count_0shot += 1
                            if predicted_plan == expected_plan:
                                state.correct_output_count_0shot += 1
                                correct_status = True
                    elif prompt_type == "prompt_5shot":
                        state.expected_outputs_5shot.append(expected_plan)
                        state.predicted_outputs_5shot.append(predicted_plan)
                        if error_type is None:
                            state.no_error_count_5shot += 1
                            if predicted_plan == expected_plan:
                                state.correct_output_count_5shot += 1
                                correct_status = True

                    timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                    line = (
                        f"{key}. [{timestamp}] | PROMPT TYPE: {prompt_type} | Correct: {correct_status} | ANSWER: {predicted_plan} "
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

                    with open("DS-R1-FULL_code_trip_results.json", "r+") as json_file:
                        file_data = json.load(json_file)
                        if prompt_type == "prompt_0shot":
                            file_data["0shot"].append(json_output)
                        elif prompt_type == "prompt_5shot":
                            file_data["5shot"].append(json_output)
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
        accuracy_5shot = (state.correct_output_count_5shot / len(state.expected_outputs_5shot)) * 100 if state.expected_outputs_5shot else 0
        total_accuracy = ((state.correct_output_count_0shot + state.correct_output_count_5shot) / 
                         (len(state.expected_outputs_0shot) + len(state.expected_outputs_5shot))) * 100 if (state.expected_outputs_0shot + state.expected_outputs_5shot) else 0

        no_error_accuracy_0shot = (state.correct_output_count_0shot / state.no_error_count_0shot) * 100 if state.no_error_count_0shot > 0 else 0
        no_error_accuracy_5shot = (state.correct_output_count_5shot / state.no_error_count_5shot) * 100 if state.no_error_count_5shot > 0 else 0

        accuracy_line = (
            f"\n0-shot prompts: Model guessed {state.correct_output_count_0shot} out of {len(state.expected_outputs_0shot)} correctly.\n"
            f"Accuracy: {accuracy_0shot:.2f}%\n"
            f"\n5-shot prompts: Model guessed {state.correct_output_count_5shot} out of {len(state.expected_outputs_5shot)} correctly.\n"
            f"Accuracy: {accuracy_5shot:.2f}%\n"
            f"\nTotal accuracy: {total_accuracy:.2f}%\n"
            f"\n0-shot prompts with no errors: {state.correct_output_count_0shot} out of {state.no_error_count_0shot} produced correct outputs.\n"
            f"No-error accuracy: {no_error_accuracy_0shot:.2f}%\n"
            f"\n5-shot prompts with no errors: {state.correct_output_count_5shot} out of {state.no_error_count_5shot} produced correct outputs.\n"
            f"No-error accuracy: {no_error_accuracy_5shot:.2f}%\n"
            f"\nTotal time taken: {total_runtime} seconds"
        )

        txt_file.write(accuracy_line)

if __name__ == "__main__":
    os.environ["PYTORCH_CUDA_ALLOC_CONF"] = "expandable_segments:True"
    asyncio.run(run_model())

