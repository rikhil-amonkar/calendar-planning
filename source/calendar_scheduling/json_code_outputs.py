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

# Configure logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')

# Set up the argument parser for model selection
parser = ArgumentParser(description="Select a HuggingFace model.")
parser.add_argument('--model', type=str, required=True, help="The HuggingFace model ID to use.")
args = parser.parse_args()

# State management
STATE_FILE = "calendar_scheduling_state_json_code.json"

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

# Load the prompts from the JSON file
def load_prompts(file_path):
    try:
        with open(file_path, "r") as file:
            prompts = json.load(file)
            return prompts
    except Exception as e:
        logging.error(f"Error loading prompts: {e}")
        raise

# Define prefix and suffix messages
prefix_message = (
    "You are an expert at scheduling meetings. Your task is to find a suitable time for a meeting "
    "based on the participants' schedules and constraints. In this case:\n"
)
suffix_message = (
    "\nGenerate a fully working Python script with code that calculates a proposed time and outputs it in the format HH:MM:HH:MM. "
    "The script should also output the day of the week (e.g., Monday, Tuesday). "
    "The script should be clean, well-formatted, and enclosed within '''python and '''. "
    "The output of the generated code must include both the time range (like {14:30:15:30}) and the day of the week. "
    "Provide the response with only code."
)

# Initialize the model engine
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

# Function to extract the code from the model's response
def extract_code(response):
    delimiters = ["'''python", "'''", "```python", "```"]
    
    start = -1
    for delimiter in delimiters:
        start = response.find(delimiter)
        if start != -1:
            start += len(delimiter)
            break
    
    if start == -1:
        return None
    
    end = -1
    for delimiter in delimiters:
        end = response.find(delimiter, start)
        if end != -1:
            break
    
    if end == -1:
        return None
    
    return response[start:end].strip()

# Function to remove leading zeros from times
def remove_leading_zeros(time_str):
    if not time_str:
        return None
    parts = time_str.strip("{}").split(":")
    if len(parts) != 4:
        return time_str
    parts[0] = str(int(parts[0]))
    parts[2] = str(int(parts[2]))
    return f"{{{':'.join(parts)}}}"

# Function to normalize time format
def normalize_time_format(time_str):
    if not time_str:
        return None
    time_pattern = re.compile(r"\b\d{2}:\d{2}:\d{2}:\d{2}\b")
    match = time_pattern.search(time_str)
    if match:
        time_str = match.group(0)
        time_str = remove_leading_zeros(time_str)
        return time_str
    return None

# Function to run the generated Python script and capture its output
def run_generated_code(code):
    try:
        with open("generated_code_basic.py", "w") as file:
            file.write(code)
        result = subprocess.run(["python", "generated_code_basic.py"], 
                              capture_output=True, text=True, check=True)
        output = result.stdout.strip()
        
        # Extract day and time from the output
        day_match = re.search(r'(Monday|Tuesday|Wednesday|Thursday|Friday|Saturday|Sunday)', 
                             output, re.IGNORECASE)
        day = day_match.group(0) if day_match else None
        
        time_output = normalize_time_format(output)
        
        return time_output, day, False  # No error occurred
    except subprocess.CalledProcessError:
        return None, None, True  # Error occurred
    except Exception:
        return None, None, True  # Error occurred

# Function to parse the golden plan time into day and time format
def parse_golden_plan(golden_plan):
    match = re.search(r'(\w+), (\d{1,2}:\d{2}) - (\d{1,2}:\d{2})', golden_plan)
    if match:
        day_of_week, start_time, end_time = match.groups()
        time_range = f"{{{start_time}:{end_time}}}"
        return day_of_week, time_range
    return "Invalid day format", "Invalid time format"

# Function to stop the model's response after the second '''
def stop_after_second_triple_quote(response):
    first_triple_quote = response.find("'''")
    if first_triple_quote == -1:
        return response
    second_triple_quote = response.find("'''", first_triple_quote + 3)
    if second_triple_quote == -1:
        return response
    return response[:second_triple_quote + 3]

# Function to initialize the JSON results file
def initialize_results_file(file_path):
    if not os.path.exists(file_path):
        with open(file_path, "w") as json_file:
            json.dump({"0shot": []}, json_file, indent=4)

# Main function to run the model
async def run_model():
    # Initialize state
    state = EvaluationState()
    state_loaded = state.load()

    prompts_data = load_prompts("../../data/calendar_scheduling_100.json")
    prompts_list = list(prompts_data.items())

    engine = initialize_engine(args.model)
    ai = Kani(engine)

    # Determine file open mode
    txt_mode = 'a' if state_loaded and not state.first_run else 'w'
    json_results_file = "DS-R1-DL-70B_code_calendar_results.json"
    txt_results_file = "DS-R1-DL-70B_code_calendar_results.txt"

    # Ensure the JSON file exists with the correct structure
    if not os.path.exists(json_results_file) or not state_loaded:
        initialize_results_file(json_results_file)

    with open(txt_results_file, txt_mode) as txt_file:
        # Write header if this is a fresh run
        if not state_loaded or state.first_run:
            initialize_results_file(json_results_file)
            state.first_run = False

        for key, data in prompts_list:
            # Skip already processed examples
            if key in state.processed_examples:
                continue

            for prompt_type in ["prompt_0shot"]:
                if prompt_type in data:
                    prompt = data[prompt_type]
                    golden_plan = data["golden_plan"]
                    full_prompt = prefix_message + prompt + suffix_message

                    try:
                        response = await ai.chat_round_str(full_prompt)
                        response = stop_after_second_triple_quote(response)
                        code = extract_code(response)
                        
                        if code:
                            code_output, day_output, has_error = run_generated_code(code)
                            predicted_time = code_output if code_output else None
                            predicted_day = day_output if day_output else None
                        else:
                            predicted_time = None
                            predicted_day = None
                            has_error = True

                        expected_day, expected_time = parse_golden_plan(golden_plan)

                        if prompt_type == "prompt_0shot":
                            state.expected_outputs_0shot.append((expected_day, expected_time))
                            state.predicted_outputs_0shot.append((predicted_day, predicted_time))
                            if not has_error:
                                state.no_error_count_0shot += 1
                                if predicted_time == expected_time and predicted_day == expected_day:
                                    state.correct_output_count_0shot += 1

                        timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                        line = (
                            f"{key}. [{timestamp}] | PROMPT TYPE: {prompt_type} | "
                            f"ANSWER: {predicted_time}, {predicted_day} | "
                            f"EXPECTED: {expected_time}, {expected_day} | "
                            f"ERROR: {'Yes' if has_error else 'No'}"
                        )
                        logging.info(line)
                        txt_file.write(line + "\n")

                        # JSON output format
                        json_output = {
                            "final_program_time": {
                                "day": predicted_day,
                                "start_time": predicted_time.split(":")[0] + ":" + predicted_time.split(":")[1] if predicted_time else None,
                                "end_time": predicted_time.split(":")[2] + ":" + predicted_time.split(":")[3] if predicted_time else None
                            },
                            "expected_time": {
                                "day": expected_day,
                                "start_time": expected_time.split(":")[0] + ":" + expected_time.split(":")[1] if expected_time else None,
                                "end_time": expected_time.split(":")[2] + ":" + expected_time.split(":")[3] if expected_time else None
                            },
                            "has_error": has_error,
                            "raw_model_response": response,
                            "count": key
                        }

                        with open(json_results_file, "r+") as json_file:
                            file_data = json.load(json_file)
                            file_data["0shot"].append(json_output)
                            json_file.seek(0)
                            json.dump(file_data, json_file, indent=4)
                            json_file.truncate()

                        # Update processed examples and save state
                        state.processed_examples.add(key)
                        state.save()

                        # Clear memory
                        del response, code, code_output, predicted_time, predicted_day, has_error, json_output
                        gc.collect()
                        torch.cuda.empty_cache()

                    except Exception as e:
                        logging.error(f"Error processing prompt {key}: {e}")

    # Final results
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

    with open(txt_results_file, "a") as file:
        file.write(accuracy_line)

# Run the model
if __name__ == "__main__":
    # Set environment variable to reduce memory fragmentation
    os.environ["PYTORCH_CUDA_ALLOC_CONF"] = "expandable_segments:True"
    asyncio.run(run_model())