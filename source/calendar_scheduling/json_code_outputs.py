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
STATE_FILE = "meeting_scheduling_state_json_code.json"

class EvaluationState:
    def __init__(self):
        self.expected_outputs_0shot = []
        self.predicted_outputs_0shot = []
        # self.expected_outputs_5shot = []
        # self.predicted_outputs_5shot = []
        self.start_time = datetime.now()
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
    "\nGenerate a full, working Python script with real code that calculates a proposed time and outputs it in the format HH:MM:HH:MM. " \
    "The Python script should have actual code, be clean, well-formatted. " \
    "The output of the generated code must be a valid time, like {14:30:15:30}. " \
    "Provide minimal text with a complete response of code. Answer briefly and directly. Limit your response to the essential information." \
    "Make sure the time found by the code is a valid time based on the task."
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

# Function to remove leading zeros from times in the format HH:MM:HH:MM
def remove_leading_zeros(time_str):
    if not time_str:
        return None
    # Split the time string into parts
    parts = time_str.strip("{}").split(":")
    if len(parts) != 4:
        return time_str  # Return the original string if the format is incorrect
    # Remove leading zeros from each hour part
    parts[0] = str(int(parts[0]))  # First hour
    parts[2] = str(int(parts[2]))  # Second hour
    # Reconstruct the time string
    return f"{{{':'.join(parts)}}}"

# Modify the normalize_time_format function to use remove_leading_zeros
def normalize_time_format(time_str):
    if not time_str:
        return None
    
    # Use a regex to find four numbers in the format HH:MM:HH:MM, HH:MM-HH:MM, or HHMMHHMM
    time_pattern = re.compile(r"(\d{1,2})[:-]?(\d{2})[:-]?(\d{1,2})[:-]?(\d{2})")
    match = time_pattern.search(time_str)
    
    if match:
        # Extract the four numbers (hours and minutes)
        start_hour, start_minute, end_hour, end_minute = match.groups()
        
        # Ensure two-digit format for hours and minutes
        start_hour = f"{int(start_hour):02d}"
        start_minute = f"{int(start_minute):02d}"
        end_hour = f"{int(end_hour):02d}"
        end_minute = f"{int(end_minute):02d}"
        
        # Reformat into the consistent format {HH:MM:HH:MM}
        normalized_time = f"{{{start_hour}:{start_minute}:{end_hour}:{end_minute}}}"
        return normalized_time
    
    return None

# Function to categorize errors
def categorize_error(error_message):
    error_types = ["SyntaxError", "IndentationError", "NameError", "TypeError", "ValueError", "ImportError", "RuntimeError", "AttributeError", "KeyError", "IndexError"]
    for error_type in error_types:
        if error_type in error_message:
            return error_type
    return "Other"

# Function to run the generated Python script and capture its output
def run_generated_code(code):
    try:
        with open("generated_code_json_code_cal.py", "w") as file:
            file.write(code)
        result = subprocess.run(["python", "generated_code_json_code_cal.py"], capture_output=True, text=True, check=True)
        output = result.stdout.strip()
        output = normalize_time_format(output)
        output = remove_leading_zeros(output)
        return output, None
    except subprocess.CalledProcessError as e:
        error_type = categorize_error(e.stderr)
        return None, error_type

# Function to convert the golden plan to dictionary format
def convert_golden_plan(golden_plan):
    if "Here is the proposed time:" in golden_plan:
        time_part = golden_plan.split(": ")[-1].strip()
        start_time, end_time = time_part.split(" - ")
        start_time = start_time.split(", ")[-1] if ", " in start_time else start_time
        end_time = end_time.split(", ")[-1] if ", " in end_time else end_time
        time_range = f"{{{start_time}:{end_time}}}"
        return time_range
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

    prompts_data = load_prompts("../../data/calendar_scheduling_100.json")
    prompts_list = list(prompts_data.items())

    engine = initialize_engine(args.model)
    ai = Kani(engine)

    # Determine file open mode
    txt_mode = 'a' if state_loaded and not state.first_run else 'w'

    # Ensure the JSON file exists with the correct structure
    if not os.path.exists("DS-R1-DL-70B_json_coderesults.json") or not state_loaded:
        with open("DS-R1-DL-70B_json_coderesults.json", "w") as json_file:
            json.dump({"0shot": []}, json_file, indent=4)

    with open("DS-R1-DL-70B_text_coderesults.txt", txt_mode) as txt_file:
        # Write header if this is a fresh run
        if not state_loaded or state.first_run:
            with open("DS-R1-DL-70B_json_coderesults.json", "w") as json_file:
                json.dump({"0shot": []}, json_file, indent=4)
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
                    correct_status = False

                    try:
                        response = await ai.chat_round_str(full_prompt)
                        # Stop the response after the second '''
                        response = stop_after_second_triple_quote(response)
                        code = extract_code(response)
                        if code:
                            code_output, error_type = run_generated_code(code)
                            predicted_time = code_output if code_output else None
                        else:
                            predicted_time = None
                            error_type = "NoCodeGenerated"

                        expected_time = convert_golden_plan(golden_plan)

                        if prompt_type == "prompt_0shot":
                            state.expected_outputs_0shot.append(expected_time)
                            state.predicted_outputs_0shot.append(predicted_time)
                            if error_type is None:
                                state.no_error_count_0shot += 1
                                if predicted_time == expected_time:
                                    state.correct_output_count_0shot += 1
                                    correct_status = True

                        timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                        line = (
                            f"{key}. [{timestamp}] | PROMPT TYPE: {prompt_type} | ANSWER: {predicted_time} "
                            f"EXPECTED: {expected_time} | ERROR: {error_type}"
                        )
                        logging.info(line)
                        txt_file.write(line + "\n")

                        json_output = {
                            "final_program_time": predicted_time,
                            "expected_time": expected_time,
                            "type_error": error_type,
                            "full_response": response,
                            "count": key,
                            "is_correct": correct_status
                        }

                        with open("DS-R1-DL-70B_json_coderesults.json", "r+") as json_file:
                            file_data = json.load(json_file)
                            if prompt_type == "prompt_0shot":
                                file_data["0shot"].append(json_output)
                            json_file.seek(0)
                            json.dump(file_data, json_file, indent=4)
                            json_file.truncate()

                        # Update processed examples and save state
                        state.processed_examples.add(key)
                        state.save()

                        # Clear memory
                        del response, code, code_output, predicted_time, expected_time, error_type, json_output
                        gc.collect()
                        torch.cuda.empty_cache()

                    except Exception as e:
                        logging.error(f"Error processing prompt {key}: {e}")

    # Final results
    end_time = datetime.now()
    total_runtime = state.previous_time + (end_time - state.start_time).total_seconds()
    
    accuracy_0shot = (state.correct_output_count_0shot / len(state.expected_outputs_0shot)) * 100 if state.expected_outputs_0shot else 0
    # total_accuracy = accuracy_0shot  # Since we're only using 0-shot now

    no_error_accuracy_0shot = (state.correct_output_count_0shot / state.no_error_count_0shot) * 100 if state.no_error_count_0shot > 0 else 0

    accuracy_line = (
        f"\n0-shot prompts: Model guessed {state.correct_output_count_0shot} out of {len(state.expected_outputs_0shot)} correctly.\n"
        f"Accuracy: {accuracy_0shot:.2f}%\n"
        f"\n0-shot prompts with no errors: {state.correct_output_count_0shot} out of {state.no_error_count_0shot} produced correct outputs.\n"
        f"No-error accuracy: {no_error_accuracy_0shot:.2f}%\n"
        f"\nTotal time taken: {total_runtime} seconds"
    )

    with open("DS-R1-DL-70B_text_coderesults.txt", "a") as file:
        file.write(accuracy_line)

# Run the model
if __name__ == "__main__":
    # Set enviroment variable to reduce memory fragmentation
    os.environ["PYTORCH_CUDA_ALLOC_CONF"] = "expandable_segments:True"
    asyncio.run(run_model())



# import asyncio
# import json
# import logging
# import os
# import re
# import subprocess
# from argparse import ArgumentParser
# from datetime import datetime
# from kani import Kani
# from kani.engines.huggingface import HuggingEngine
# import torch
# import gc

# # Configure logging
# logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')

# # Set up the argument parser for model selection
# parser = ArgumentParser()
# parser.add_argument("--model", dest="model", help="Model name to use", required=True)
# args = parser.parse_args()

# # Load the prompts from the JSON file
# def load_prompts(file_path):
#     try:
#         with open(file_path, "r") as file:
#             prompts = json.load(file)
#             return prompts
#     except Exception as e:
#         logging.error(f"Error loading prompts: {e}")
#         raise

# # Define prefix and suffix messages
# prefix_message = (
#     "You are an expert at scheduling meetings. Your task is to find a suitable time for a meeting "
#     "based on the participants' schedules and constraints. In this case:\n"
# )
# suffix_message = (
#     "\nGenerate a full, working Python script with real code that calculates a proposed time and outputs it in the format HH:MM:HH:MM. " \
#     "The Python script should have actual code, be clean, well-formatted. " \
#     "The output of the generated code must be a valid time, like {14:30:15:30}. " \
#     "Provide minimal text with a complete response of code. Answer briefly and directly. Limit your response to the essential information." \
#     "Make sure the time found by the code is a valid time based on the task."
# )

# # Initialize the model engine
# def initialize_engine(model_id):
#     try:
#         engine = HuggingEngine(
#             model_id=model_id
#             # top_p=0.1,  # Use top-p (nucleus) sampling
#             # temperature=0.2,  # Adjust temperature
#             # do_sample=True,  # Enable sampling
#             # repetition_penalty=1.4,  # Reduce repetition
#             # max_new_tokens=3000,  # Limit the number of tokens generated
#             # top_k=50,  # Limit sampling to top 50 tokens
#             # num_beams=2, # Limit beam search
#         )
#         return engine
#     except Exception as e:
#         logging.error(f"Error initializing model: {e}")
#         raise

# # Function to extract the code from the model's response
# def extract_code(response):
#     # Define the possible code block delimiters
#     delimiters = ["'''python", "'''", "```python", "```"]
    
#     # Find the start of the code block
#     start = -1
#     for delimiter in delimiters:
#         start = response.find(delimiter)
#         if start != -1:
#             start += len(delimiter)  # Move the start index to the end of the delimiter
#             break
    
#     # If no delimiter is found, return None
#     if start == -1:
#         return None
    
#     # Find the end of the code block
#     end = -1
#     for delimiter in delimiters:
#         end = response.find(delimiter, start)  # Search for the closing delimiter after the start
#         if end != -1:
#             break
    
#     # If no closing delimiter is found, return None
#     if end == -1:
#         return None
    
#     # Extract and return the code block
#     return response[start:end].strip()

# # Function to remove leading zeros from times in the format HH:MM:HH:MM
# def remove_leading_zeros(time_str):
#     if not time_str:
#         return None
#     # Split the time string into parts
#     parts = time_str.strip("{}").split(":")
#     if len(parts) != 4:
#         return time_str  # Return the original string if the format is incorrect
#     # Remove leading zeros from each hour part
#     parts[0] = str(int(parts[0]))  # First hour
#     parts[2] = str(int(parts[2]))  # Second hour
#     # Reconstruct the time string
#     return f"{{{':'.join(parts)}}}"

# # Modify the normalize_time_format function to use remove_leading_zeros
# def normalize_time_format(time_str):
#     if not time_str:
#         return None
    
#     # Use a regex to find four numbers in the format HH:MM:HH:MM, HH:MM-HH:MM, or HHMMHHMM
#     time_pattern = re.compile(r"(\d{1,2})[:-]?(\d{2})[:-]?(\d{1,2})[:-]?(\d{2})")
#     match = time_pattern.search(time_str)
    
#     if match:
#         # Extract the four numbers (hours and minutes)
#         start_hour, start_minute, end_hour, end_minute = match.groups()
        
#         # Ensure two-digit format for hours and minutes
#         start_hour = f"{int(start_hour):02d}"
#         start_minute = f"{int(start_minute):02d}"
#         end_hour = f"{int(end_hour):02d}"
#         end_minute = f"{int(end_minute):02d}"
        
#         # Reformat into the consistent format {HH:MM:HH:MM}
#         normalized_time = f"{{{start_hour}:{start_minute}:{end_hour}:{end_minute}}}"
#         return normalized_time
    
#     return None

# # Function to categorize errors
# def categorize_error(error_message):
#     error_types = ["SyntaxError", "IndentationError", "NameError", "TypeError", "ValueError", "ImportError", "RuntimeError", "AttributeError", "KeyError", "IndexError"]
#     for error_type in error_types:
#         if error_type in error_message:
#             return error_type
#     return "Other"

# # Function to run the generated Python script and capture its output
# def run_generated_code(code):
#     try:
#         with open("generated_code.py", "w") as file:
#             file.write(code)
#         result = subprocess.run(["python", "generated_code.py"], capture_output=True, text=True, check=True)
#         output = result.stdout.strip()
#         output = normalize_time_format(output)
#         output = remove_leading_zeros(output)
#         return output, None
#     except subprocess.CalledProcessError as e:
#         error_type = categorize_error(e.stderr)
#         return None, error_type

# # Function to convert the golden plan to dictionary format
# def convert_golden_plan(golden_plan):
#     if "Here is the proposed time:" in golden_plan:
#         time_part = golden_plan.split(": ")[-1].strip()
#         start_time, end_time = time_part.split(" - ")
#         start_time = start_time.split(", ")[-1] if ", " in start_time else start_time
#         end_time = end_time.split(", ")[-1] if ", " in end_time else end_time
#         time_range = f"{{{start_time}:{end_time}}}"
#         return time_range
#     return None

# # Function to stop the model's response after the second '''
# def stop_after_second_triple_quote(response):
#     first_triple_quote = response.find("'''")
#     if first_triple_quote == -1:
#         return response  # No triple quotes found
#     second_triple_quote = response.find("'''", first_triple_quote + 3)
#     if second_triple_quote == -1:
#         return response  # Only one triple quote found
#     return response[:second_triple_quote + 3]  # Stop after the second triple quote

# # Main function to run the model
# async def run_model():
#     expected_outputs_0shot = []
#     predicted_outputs_0shot = []
#     expected_outputs_5shot = []
#     predicted_outputs_5shot = []
#     start_time = datetime.now()

#     prompts_data = load_prompts("100_prompt_scheduling.json")
#     prompts_list = list(prompts_data.items())

#     engine = initialize_engine(args.model)
#     ai = Kani(engine)

#     no_error_count_0shot = 0
#     correct_output_count_0shot = 0
#     no_error_count_5shot = 0
#     correct_output_count_5shot = 0

#     # Ensure the JSON file exists with the correct structure
#     if not os.path.exists("ML-ML-3.1-8B_json_coderesults.json"):
#         with open("ML-ML-3.1-8B_json_coderesults.json", "w") as json_file:
#             json.dump({"0shot": [], "5shot": []}, json_file, indent=4)

#     # Define the starting point
#     start_from_prompt = "calendar_scheduling_example_0"  # Change this to your desired starting prompt
#     start_processing = False  # Flag to indicate when to start processing

#     for key, data in prompts_list:
#         # Skip prompts until we reach the desired starting point
#         if key == start_from_prompt:
#             start_processing = True

#         if not start_processing:
#             logging.info(f"Skipping prompt: {key}")
#             continue  # Skip this prompt

#         for prompt_type in ["prompt_0shot"]:
#             if prompt_type in data:
#                 prompt = data[prompt_type]
#                 golden_plan = data["golden_plan"]
#                 full_prompt = prefix_message + prompt + suffix_message

#                 try:
#                     response = await ai.chat_round_str(full_prompt)
#                     # Stop the response after the second '''
#                     response = stop_after_second_triple_quote(response)
#                     code = extract_code(response)
#                     if code:
#                         code_output, error_type = run_generated_code(code)
#                         predicted_time = code_output if code_output else None
#                     else:
#                         predicted_time = None
#                         error_type = "NoCodeGenerated"

#                     expected_time = convert_golden_plan(golden_plan)

#                     if prompt_type == "prompt_0shot":
#                         expected_outputs_0shot.append(expected_time)
#                         predicted_outputs_0shot.append(predicted_time)
#                         if error_type is None:
#                             no_error_count_0shot += 1
#                             if predicted_time == expected_time:
#                                 correct_output_count_0shot += 1
#                     # elif prompt_type == "prompt_5shot":
#                     #     expected_outputs_5shot.append(expected_time)
#                     #     predicted_outputs_5shot.append(predicted_time)
#                     #     if error_type is None:
#                     #         no_error_count_5shot += 1
#                     #         if predicted_time == expected_time:
#                     #             correct_output_count_5shot += 1

#                     timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
#                     line = (
#                         f"{key}. [{timestamp}] | PROMPT TYPE: {prompt_type} | ANSWER: {predicted_time} "
#                         f"EXPECTED: {expected_time} | ERROR: {error_type}"
#                     )
#                     logging.info(line)

#                     with open("ML-ML-3.1-8B_text_coderesults.txt", "a") as file:
#                         file.write(line + "\n")

#                     json_output = {
#                         "final_program_time": predicted_time,
#                         "expected_time": expected_time,
#                         "type_error": error_type,
#                         "full_response": response,
#                         "count": key
#                     }

#                     with open("ML-ML-3.1-8B_json_coderesults.json", "r+") as json_file:
#                         file_data = json.load(json_file)
#                         if prompt_type == "prompt_0shot":
#                             file_data["0shot"].append(json_output)
#                         # elif prompt_type == "prompt_5shot":
#                         #     file_data["5shot"].append(json_output)
#                         json_file.seek(0)
#                         json.dump(file_data, json_file, indent=4)
#                         json_file.truncate()

#                     # Clear memory
#                     del response, code, code_output, predicted_time, expected_time, error_type, json_output
#                     gc.collect()
#                     torch.cuda.empty_cache()

#                 except Exception as e:
#                     logging.error(f"Error processing prompt {key}: {e}")

#     end_time = datetime.now()
#     total_time = (end_time - start_time).total_seconds()

#     accuracy_0shot = (correct_output_count_0shot / len(expected_outputs_0shot)) * 100 if expected_outputs_0shot else 0
#     # accuracy_5shot = (correct_output_count_5shot / len(expected_outputs_5shot)) * 100 if expected_outputs_5shot else 0
#     # total_accuracy = ((correct_output_count_0shot + correct_output_count_5shot) / (len(expected_outputs_0shot) + len(expected_outputs_5shot))) * 100 if (expected_outputs_0shot + expected_outputs_5shot) else 0

#     no_error_accuracy_0shot = (correct_output_count_0shot / no_error_count_0shot) * 100 if no_error_count_0shot > 0 else 0
#     # no_error_accuracy_5shot = (correct_output_count_5shot / no_error_count_5shot) * 100 if no_error_count_5shot > 0 else 0

#     accuracy_line = (
#         f"\n0-shot prompts: Model guessed {correct_output_count_0shot} out of {len(expected_outputs_0shot)} correctly.\n"
#         f"Accuracy: {accuracy_0shot:.2f}%\n"
#         # f"\n5-shot prompts: Model guessed {correct_output_count_5shot} out of {len(expected_outputs_5shot)} correctly.\n"
#         # f"Accuracy: {accuracy_5shot:.2f}%\n"
#         # f"\nTotal accuracy: {total_accuracy:.2f}%\n"
#         f"\n0-shot prompts with no errors: {correct_output_count_0shot} out of {no_error_count_0shot} produced correct outputs.\n"
#         f"No-error accuracy: {no_error_accuracy_0shot:.2f}%\n"
#         # f"\n5-shot prompts with no errors: {correct_output_count_5shot} out of {no_error_count_5shot} produced correct outputs.\n"
#         # f"No-error accuracy: {no_error_accuracy_5shot:.2f}%\n"
#         f"\nTotal time taken: {total_time} seconds"
#     )

#     with open("ML-ML-3.1-8B_text_coderesults.txt", "a") as file:
#         file.write(accuracy_line)

# # Run the model
# if __name__ == "__main__":
#     # Set enviroment variable to reduce memory fragmentation
#     os.environ["PYTORCH_CUDA_ALLOC_CONF"] = "expandable_segments:True"
#     asyncio.run(run_model())


