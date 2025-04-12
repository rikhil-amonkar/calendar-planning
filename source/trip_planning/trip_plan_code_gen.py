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
parser = ArgumentParser()
parser.add_argument("--model", dest="model", help="Model name to use", required=True)
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
    "You are an expert at trip plannong. Your task is to find a suitable itinerary "
    "based on the participants' plan, requests, and constraints. In this case:\n"
)
suffix_message = (
    "\nGenerate a full, working Python script with real code that calculates a proposed itinerary trip plan and outputs it in a JSON dictionary format. " \
    "The Python script should have actual code, be clean, well-formatted. When run, it should calculate the best plan and output the JSON trip plan." \
    "The output of the generated code must be a valid time, such as: [{'day_range': 'Day 1-5', 'place': 'Helsinki'}, {'flying': 'Day 5-5', 'from': 'Helsinki', 'to': 'Barcelona'}, {'day_range': 'Day 5-9', 'place': 'Barcelona'}, {'flying': 'Day 9-9', 'from': 'Barcelona', 'to': 'Florence'}, {'day_range': 'Day 9-14', 'place': 'Florence'}] " \
    "Provide no text with only a complete response of code. Answer briefly and directly. Limit your response to the essential information." \
    "Make sure the trip plan found by the code is a valid time based on the task and is valid JSON dictionary format. " \
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
    # Define the possible code block delimiters
    delimiters = ["'''python", "'''", "```python", "```"]
    
    # Find the start of the code block
    start = -1
    for delimiter in delimiters:
        start = response.find(delimiter)
        if start != -1:
            start += len(delimiter)  # Move the start index to the end of the delimiter
            break
    
    # If no delimiter is found, return None
    if start == -1:
        return None
    
    # Find the end of the code block
    end = -1
    for delimiter in delimiters:
        end = response.find(delimiter, start)  # Search for the closing delimiter after the start
        if end != -1:
            break
    
    # If no closing delimiter is found, return None
    if end == -1:
        return None
    
    # Extract and return the code block
    return response[start:end].strip()

# Function to categorize errors
def categorize_error(error_message):
    error_types = ["SyntaxError", "IndentationError", "NameError", "TypeError", "ValueError", "ImportError", "RuntimeError", "AttributeError"]
    for error_type in error_types:
        if error_type in error_message:
            return error_type
    return "Other"

# Function to run the generated Python script and capture its output
def run_generated_code(code):
    try:
        with open("generated_code.py", "w") as file:
            file.write(code)
        result = subprocess.run(["python", "generated_code.py"], capture_output=True, text=True, check=True)
        output = result.stdout.strip()
        return output, None
    except subprocess.CalledProcessError as e:
        error_type = categorize_error(e.stderr)
        return None, error_type

# Function to parse the golden plan into structured itinerary format
def parse_golden_plan(golden_plan):
    """Parse the golden plan into structured itinerary format matching our JSON schema."""
    itinerary = []
    
    # Split the plan into lines and process each line
    for line in golden_plan.split('\n'):
        line = line.strip()
        if not line or not line.startswith('**Day'):
            continue
            
        # Extract day range
        day_match = re.search(r'Day (\d+)(?:-(\d+))?', line)
        if not day_match:
            continue
            
        start_day = int(day_match.group(1))
        end_day = int(day_match.group(2)) if day_match.group(2) else start_day
        day_range = f"Day {start_day}-{end_day}"
        
        # Handle flying days
        if "Fly from" in line:
            fly_match = re.search(r'Fly from ([^\s,.]+) to ([^\s,.]+)', line)
            if fly_match:
                itinerary.append({
                    "flying": day_range,
                    "from": fly_match.group(1),
                    "to": fly_match.group(2)
                })
            continue
        # Handle regular days
        elif "Arriving in" in line:
            place = re.search(r'Arriving in ([^\s,.]+)', line).group(1)
        elif "Visit" in line:
            place = re.search(r'Visit ([^\s,.]+)', line).group(1)
        else:
            continue  # skip if we couldn't determine the type
            
        # Add to itinerary
        itinerary.append({
            "day_range": day_range,
            "place": place
        })
    
    return itinerary

# Function to parse the model's JSON output
def parse_model_output(model_output):
    """Parse the model's JSON output into structured itinerary format matching our JSON schema."""
    if not model_output:
        return None
    
    try:
        # If the output is already a string, parse it as JSON
        if isinstance(model_output, str):
            itinerary = json.loads(model_output)
        else:
            itinerary = model_output
        
        # Normalize the format to match the expected output
        normalized_itinerary = []
        for item in itinerary:
            # Handle both dict and list formats
            if isinstance(item, dict):
                normalized_item = {}
                
                # Handle day_range items
                if "day_range" in item:
                    normalized_item["day_range"] = item["day_range"]
                    normalized_item["place"] = item["place"]
                
                # Handle flying items
                elif "flying" in item:
                    normalized_item["flying"] = item["flying"]
                    normalized_item["from"] = item["from"]
                    normalized_item["to"] = item["to"]
                
                # Handle other potential formats
                elif "place" in item and "days" in item:
                    # Convert "days": "1-7" to "day_range": "Day 1-7"
                    days = item["days"].split("-")
                    normalized_item["day_range"] = f"Day {days[0]}-{days[1]}"
                    normalized_item["place"] = item["place"]
                
                elif "flight_day" in item:
                    # Convert "flight_day": "7" to "flying": "Day 7-7"
                    normalized_item["flying"] = f"Day {item['flight_day']}-{item['flight_day']}"
                    normalized_item["from"] = item["from"]
                    normalized_item["to"] = item["to"]
                
                else:
                    continue  # skip unrecognized formats
                
                normalized_itinerary.append(normalized_item)
        
        return normalized_itinerary
    
    except json.JSONDecodeError:
        return None
    except Exception as e:
        logging.error(f"Error parsing model output: {e}")
        return None

# Function to stop the model's response after the second '''
def stop_after_second_triple_quote(response):
    first_triple_quote = response.find("'''")
    if first_triple_quote == -1:
        return response  # No triple quotes found
    second_triple_quote = response.find("'''", first_triple_quote + 3)
    if second_triple_quote == -1:
        return response  # Only one triple quote found
    return response[:second_triple_quote + 3]  # Stop after the second triple quote

# Main function to run the model
async def run_model():
    # Initialize state
    state = EvaluationState()
    state_loaded = state.load()

    # Determine file open mode
    txt_mode = 'a' if state_loaded and not state.first_run else 'w'

    prompts_data = load_prompts("100_trip_planning_examples.json")
    prompts_list = list(prompts_data.items())

    engine = initialize_engine(args.model)
    ai = Kani(engine)

    # Ensure the JSON file exists with the correct structure
    if not os.path.exists("ML-L-3.1-70B_code_trip_results.json") or not state_loaded:
        with open("ML-L-3.1-70B_code_trip_results.json", "w") as json_file:
            json.dump({"0shot": [], "5shot": []}, json_file, indent=4)

    with open("ML-L-3.1-70B_code_trip_results.txt", txt_mode) as txt_file:
        # Write header if this is a fresh run
        if not state_loaded or state.first_run:
            txt_file.write("=== New Run Started ===\n")
            with open("ML-L-3.1-70B_code_trip_results.json", "w") as json_file:
                json.dump({"0shot": [], "5shot": []}, json_file, indent=4)
            state.first_run = False

        for key, data in prompts_list:
            # Skip already processed examples
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
                    response = await ai.chat_round_str(full_prompt)
                    # Stop the response after the second '''
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
                        "full_response": response,
                        "count": key,
                        "is_correct": correct_status
                    }

                    # Update JSON file
                    with open("ML-L-3.1-70B_code_trip_results.json", "r+") as json_file:
                        file_data = json.load(json_file)
                        if prompt_type == "prompt_0shot":
                            file_data["0shot"].append(json_output)
                        elif prompt_type == "prompt_5shot":
                            file_data["5shot"].append(json_output)
                        json_file.seek(0)
                        json.dump(file_data, json_file, indent=4)
                        json_file.truncate()

                    # Update processed examples and save state
                    state.processed_examples.add(key)
                    state.save()

                    # Clear memory
                    del response, code, code_output, predicted_plan, expected_plan, error_type, json_output
                    gc.collect()
                    torch.cuda.empty_cache()

                except Exception as e:
                    logging.error(f"Error processing prompt {key}: {e}")

        # Final results
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

# Run the model
if __name__ == "__main__":
    # Set environment variable to reduce memory fragmentation
    os.environ["PYTORCH_CUDA_ALLOC_CONF"] = "expandable_segments:True"
    asyncio.run(run_model())