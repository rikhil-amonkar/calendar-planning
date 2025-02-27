  
#*****************WORKING JSON FORCE CODE*************************************

import argparse
import asyncio
import json
import datetime
import outlines
import transformers
import re
from kani import Kani
from kani.engines.huggingface import HuggingEngine

# Define the JSON schema for the time range output
JSON_SCHEMA = {
    "type": "object",
    "properties": {
        "time_range": {"type": "string"}
    },
    "required": ["time_range"]
}

# Load the calendar scheduling examples from the JSON file
with open('test_scheduling.json', 'r') as file:
    calendar_examples = json.load(file)

# Argument parser to select the model
parser = argparse.ArgumentParser(description="Select a HuggingFace model.")
parser.add_argument('--model', type=str, required=True, help="The HuggingFace model ID to use.")
args = parser.parse_args()

# Load the model selected by the user
engine = HuggingEngine(model_id=args.model)

# Tokenizer setup
outlines_tokenizer = outlines.models.TransformerTokenizer(engine.tokenizer)

# JSON logits processor setup
json_logits_processor = outlines.processors.JSONLogitsProcessor(JSON_SCHEMA, outlines_tokenizer)

# Assign logits processor to the model
# engine.hyperparams["logits_processor"] = transformers.LogitsProcessorList([json_logits_processor])

# Create the Kani instance
ai = Kani(engine)

# Function to parse the golden plan time into {HH:MM:HH:MM} format
def parse_golden_plan_time(golden_plan):
    match = re.search(r'(\d{1,2}:\d{2}) - (\d{1,2}:\d{2})', golden_plan)
    if match:
        start_time, end_time = match.groups()
        return f"{{{start_time}:{end_time}}}"
    return "Invalid format"

# Initialize counters for accuracy calculation
correct_0shot = 0
correct_5shot = 0
total_0shot = 0
total_5shot = 0

# Initialize lists for JSON output
results_0shot = []
results_5shot = []

# Open the text file for writing results
with open('model_results.txt', 'w') as txt_file, open('model_results.json', 'w') as json_file:
    start_time = datetime.datetime.now()
    
    for example_id, example in calendar_examples.items():
        for prompt_type in ['prompt_0shot', 'prompt_5shot']:
            prompt = example[prompt_type]
            golden_plan = example['golden_plan']

            # Parse golden plan into {HH:MM:HH:MM} format
            expected_time = parse_golden_plan_time(golden_plan)

            # Append the suffix to the prompt
            prompt += "\n\nPlease output the proposed time in the following JSON format:\n{\"time_range\": \"HH:MM:HH:MM\"}. Make sure not to use any Python code, just the JSON direct output."
            
            # Run the model and capture the response
            async def get_model_response():
                full_response = ""
                async for token in ai.chat_round_stream(prompt):
                    full_response += token
                    print(token, end="", flush=True)
                print()  # For a newline after the response
                return full_response.strip()  # Return the actual response
            
            model_response = asyncio.run(get_model_response())

            def extract_time_range(response):
                """Extracts HH:MM:HH:MM format from the model's raw response and removes leading zeros from single-digit hours."""
                if not response or not isinstance(response, str):  # Check if response is None or not a string
                    return "Invalid response"
                
                # Extract the time range using regex
                match = re.search(r'(\d{1,2}:\d{2}):(\d{1,2}:\d{2})', response)
                if not match:
                    return "Invalid response"
                
                # Remove leading zeros from single-digit hours
                start_time = match.group(1)
                end_time = match.group(2)
                
                # Function to remove leading zeros from single-digit hours
                def remove_leading_zero(time_str):
                    parts = time_str.split(':')
                    hour = parts[0].lstrip('0')  # Remove leading zeros from the hour
                    return f"{hour}:{parts[1]}"
                
                start_time = remove_leading_zero(start_time)
                end_time = remove_leading_zero(end_time)
                
                return f"{{{start_time}:{end_time}}}"

            # Extract the time range from the model's response
            if model_response:
                model_time = extract_time_range(model_response)
            else:
                model_time = "Invalid response"     
                   
            # Print the formatted output to the terminal
            timestamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            print(f"{example_id}. [{timestamp}] | PROMPT TYPE: {prompt_type} | ANSWER: {model_time} EXPECTED: {expected_time}")

            # Write to the text file
            txt_file.write(f"{example_id}. [{timestamp}] | PROMPT TYPE: {prompt_type} | ANSWER: {model_time} EXPECTED: {expected_time}\n")
            
            # Prepare the JSON output
            result_entry = {
                "final_time": f"{model_time}",
                "expected_time": f"{expected_time}",
                "exact_response": model_response,
                "count": example_id
            }
            
            if prompt_type == 'prompt_0shot':
                results_0shot.append(result_entry)
                total_0shot += 1
                if model_time == expected_time:
                    correct_0shot += 1
            else:
                results_5shot.append(result_entry)
                total_5shot += 1
                if model_time == expected_time:
                    correct_5shot += 1
    
    # Calculate accuracies
    accuracy_0shot = (correct_0shot / total_0shot) * 100 if total_0shot > 0 else 0
    accuracy_5shot = (correct_5shot / total_5shot) * 100 if total_5shot > 0 else 0
    total_accuracy = ((correct_0shot + correct_5shot) / (total_0shot + total_5shot)) * 100 if (total_0shot + total_5shot) > 0 else 0
    
    # Write the final accuracy to the text file
    end_time = datetime.datetime.now()
    total_time = end_time - start_time
    txt_file.write(f"\n0-shot prompts: Model guessed {correct_0shot} out of {total_0shot} correctly.\n")
    txt_file.write(f"Accuracy: {accuracy_0shot:.2f}%\n")
    txt_file.write(f"5-shot prompts: Model guessed {correct_5shot} out of {total_5shot} correctly.\n")
    txt_file.write(f"Accuracy: {accuracy_5shot:.2f}%\n")
    txt_file.write(f"Total accuracy: {total_accuracy:.2f}%\n")
    txt_file.write(f"Total time taken: {total_time}\n")
    
    # Write the JSON output
    json_output = {
        "0shot": results_0shot,
        "5shot": results_5shot
    }
    json.dump(json_output, json_file, indent=4)

print("Processing complete. Results saved to model_results.txt and model_results.json.")


#*****************TEMPLATE OF FORCE JSON (TRAIN, COST)*************************************

# import argparse
# import asyncio
# import outlines
# import transformers
# from kani import Kani
# from kani.engines.huggingface import HuggingEngine

# # Define the JSON schema and prompt as before
# JSON_SCHEMA = {
#     "type": "array",
#     "items": {
#         "type": "object",
#         "properties": {
#             "from": {"type": "string"},
#             "to": {"type": "string"},
#             "train": {"type": "string"},
#             "cost": {"type": "number"},
#         },
#         "required": ["from", "to", "train", "cost"],
#     },
# }
# PROMPT = """\
# Please output a JSON list of the steps necessary to get from Iiyama to Noboribetsu by train. Your output should be a 
# list in the following format:
# [
#   {
#     "from": "Station Name (Station ID)",
#     "to": "Station Name (Station ID)",
#     "train": "Name of Train line",
#     "cost": 0  # cost in yen
#   },
#   ...
# ]
# """

# # Argument parser to select the model
# parser = argparse.ArgumentParser(description="Select a HuggingFace model.")
# parser.add_argument('--model', type=str, required=True, help="The HuggingFace model ID to use.")
# args = parser.parse_args()

# # Load the model selected by the user
# engine = HuggingEngine(model_id=args.model)

# # Tokenizer setup
# outlines_tokenizer = outlines.models.TransformerTokenizer(engine.tokenizer)

# # JSON logits processor setup
# json_logits_processor = outlines.processors.JSONLogitsProcessor(JSON_SCHEMA, outlines_tokenizer)

# # Assign logits processor to the model
# engine.hyperparams["logits_processor"] = transformers.LogitsProcessorList([json_logits_processor])

# # Create the Kani instance
# ai = Kani(engine)

# async def main():
#     async for token in ai.chat_round_stream(PROMPT):
#         print(token, end="", flush=True)
#     print()

# if __name__ == "__main__":
#     asyncio.run(main())


#*****************UNUSED JSON CODE - WORKING*************************************

# import asyncio
# import json
# import logging
# import os
# import sys
# from argparse import ArgumentParser
# from datetime import datetime, timedelta
# import torch
# import subprocess
# from kani import Kani
# from kani.engines.huggingface import HuggingEngine
# import re

# # Configure logging
# logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')

# # Set up the argument parser for model selection
# parser = ArgumentParser()
# parser.add_argument("--model", dest="model", help="Model name to use", required=True)
# args = parser.parse_args()

# # Load the prompts from the JSON file
# def load_prompts(file_path):
#     try:
#         print(f"Loading prompts from {file_path}...")  # Debug print
#         with open(file_path, "r") as file:
#             prompts = json.load(file)
#             print(f"Successfully loaded {len(prompts)} prompts.")  # Debug print
#             return prompts
#     except Exception as e:
#         print(f"Error loading prompts: {e}")  # Debug print
#         raise

# # Define prefix and suffix messages.
# prefix_message = (
#     "You are an expert at scheduling meetings. Your task is to find a suitable time for a meeting "
#     "based on the participants' schedules and constraints. Follow these rules:\n"
# )
# suffix_message = (
#     "\nWrite a full Python program with actual code that outputs the desired meeting time range in the exact format {HH:MM:HH:MM}. "
#     "Do not include any extra words, explanations, or other text. Only return the Python code. "
#     "Example output: {14:30:15:30}. I want the final time to include the curly brackets {} on the outer portion of the time, "
#     "just as the example provided. Lastly, make sure any - or , are removed and the final answer only has : in it surrounded by the time and the curly brackets, "
#     "for example: {HH:MM:HH:MM}. Please only provide one singular time answer and not multiple. The output of the Python code you generate should only have one format as {time} with HH:MM:HH:MM in between the brackets such as {9:30:10:00}."
# )

# # Initialize the model engine.
# def initialize_engine(model_id):
#     try:
#         engine = HuggingEngine(
#             model_id=model_id,
#             use_auth_token=True,
#             model_load_kwargs={
#                 "device_map": "auto",
#                 "trust_remote_code": True,
#                 "pad_token_id": 128001,
#             },
#         )
#         return engine
#     except Exception as e:
#         print(f"Error initializing model: {e}")  # Debug print
#         raise

# # Function to extract the code from the model's response
# def extract_code(response):
#     start = response.find("```python")
#     if start == -1:
#         start = response.find("```")
#     if start != -1:
#         start += len("```python") if "```python" in response else len("```")
#         end = response.find("```", start)
#         if end != -1:
#             return response[start:end].strip()
#     return None

# # Function to normalize the time format (ensure it has {} and replace spaces with colons)
# def normalize_time_format(time_str):
#     """
#     Normalize the time format to ensure it matches {HH:MM:HH:MM}.
#     If the input is invalid or contains multiple outputs, return the first valid output.
#     """
#     if not time_str:
#         return None

#     # Split the output into lines and process each line
#     lines = time_str.strip().split("\n")
#     for line in lines:
#         line = line.strip()
#         # Validate the format using regex
#         if re.match(r"^\{\d{2}:\d{2}:\d{2}:\d{2}\}$", line):
#             return line  # Return the first valid output
#     return None  # No valid output found

# # Function to categorize errors
# def categorize_error(error_message):
#     if "SyntaxError" in error_message:
#         return "SyntaxError"
#     elif "IndentationError" in error_message:
#         return "IndentationError"
#     elif "NameError" in error_message:
#         return "NameError"
#     elif "TypeError" in error_message:
#         return "TypeError"
#     elif "ValueError" in error_message:
#         return "ValueError"
#     elif "ImportError" in error_message:
#         return "ImportError"
#     elif "RuntimeError" in error_message:
#         return "RuntimeError"
#     else:
#         return "Other"

# # Function to run the generated Python script and capture its output
# def run_generated_code(code):
#     """
#     Run the generated Python script and capture its output.
#     Ensure the output is in the correct format and only one time is returned.
#     """
#     try:
#         with open("generated_code.py", "w") as file:
#             file.write(code)
#         result = subprocess.run(["python", "generated_code.py"], capture_output=True, text=True, check=True)
#         output = result.stdout.strip()
#         output = normalize_time_format(output)  # Normalize and validate the output
#         return output, None  # Return output and no error
#     except subprocess.CalledProcessError as e:
#         error_type = categorize_error(e.stderr)  # Categorize the error
#         return None, error_type  # Return None and the specific error type

# # Function to convert the golden plan to dictionary format and remove days of the week.
# def convert_golden_plan(golden_plan):
#     if "Here is the proposed time:" in golden_plan:
#         time_part = golden_plan.split(": ")[-1].strip()
#         start_time, end_time = time_part.split(" - ")
#         start_time = start_time.split(", ")[-1] if ", " in start_time else start_time
#         end_time = end_time.split(", ")[-1] if ", " in end_time else end_time
#         time_range = f"{{{start_time}:{end_time}}}"
#         return time_range
#     return None

# # Function to calculate accuracy.
# def calculate_accuracy(expected, predicted):
#     correct = sum(1 for exp, pred in zip(expected, predicted) if exp == pred)
#     accuracy = (correct / len(expected)) * 100 if expected else 0
#     print(f"Accuracy calculation: {correct} correct out of {len(expected)}.")  # Debug print
#     return accuracy

# # Function to restart the model.
# def restart_model(engine):
#     torch.cuda.empty_cache()
#     return Kani(engine)

# # Function to save checkpoint and current count.
# def save_checkpoint(index, count, total_elapsed_time, last_written_timestamp):
#     try:
#         with open("checkpoint.txt", "w") as file:
#             file.write(f"{index},{count},{total_elapsed_time},{last_written_timestamp}")
#     except Exception as e:
#         print(f"Failed to save checkpoint: {e}")  # Debug print

# # Function to load checkpoint and current count.
# def load_checkpoint():
#     if os.path.exists("checkpoint.txt"):
#         try:
#             with open("checkpoint.txt", "r") as file:
#                 checkpoint_data = file.read().strip().split(",")
#                 if len(checkpoint_data) == 4:
#                     index, count, total_elapsed_time, last_written_timestamp = checkpoint_data
#                     print(f"Loaded checkpoint: index={index}, count={count}, total_elapsed_time={total_elapsed_time}, last_written_timestamp={last_written_timestamp}")  # Debug print
#                     return int(index), int(count), float(total_elapsed_time), last_written_timestamp
#         except Exception as e:
#             print(f"Failed to load checkpoint: {e}")  # Debug print
#     return 0, 0, 0.0, None  # Default values if no checkpoint exists

# # Function to get the last written timestamp from the results file.
# def get_last_written_timestamp():
#     if os.path.exists("DS-R1-DL-8B_json_results.txt"):
#         try:
#             with open("DS-R1-DL-8B_json_results.txt", "r") as file:
#                 lines = file.readlines()
#                 if lines:
#                     last_line = lines[-1].strip()
#                     if last_line.startswith("Model Results:"):
#                         return None  # No timestamps written yet
#                     # Extract the timestamp from the last line
#                     timestamp_str = last_line.split("[")[1].split("]")[0]
#                     return datetime.strptime(timestamp_str, "%Y-%m-%d %H:%M:%S")
#         except Exception as e:
#             print(f"Failed to read last written timestamp: {e}")  # Debug print
#     return None

# # Main function to run the model.
# async def run_model():
#     expected_outputs_0shot = []
#     predicted_outputs_0shot = []
#     expected_outputs_5shot = []
#     predicted_outputs_5shot = []
#     start_time_value = datetime.now()

#     # Load checkpoint (index, count, total_elapsed_time, last_written_timestamp)
#     start_index, count, total_elapsed_time, last_written_timestamp = load_checkpoint()

#     # Initialize text results file if it doesn't exist.
#     if not os.path.exists("DS-R1-DL-8B_json_results.txt"):
#         print("Initializing text results file...")  # Debug print
#         with open("DS-R1-DL-8B_json_results.txt", "w") as file:
#             file.write("Model Results:\n")

#     # Initialize JSON results file if it doesn't exist.
#     if not os.path.exists("DS-R1-DL-8B_jsoncode_results.json"):
#         print("Initializing JSON results file...")  # Debug print
#         with open("DS-R1-DL-8B_jsoncode_results.json", "w") as json_file:
#             json.dump({"0shot": [], "5shot": []}, json_file)

#     prompts_data = load_prompts("100_prompt_scheduling.json")
#     prompts_list = list(prompts_data.items())

#     engine = initialize_engine(args.model)
#     ai = Kani(engine)

#     # Track the number of programs that executed without errors and produced correct outputs
#     no_error_count_0shot = 0
#     correct_output_count_0shot = 0
#     no_error_count_5shot = 0
#     correct_output_count_5shot = 0

#     for i in range(start_index, len(prompts_list)):
#         key, data = prompts_list[i]

#         # Get the current timestamp for the prompt being processed
#         current_timestamp = datetime.now()

#         # Get the last written timestamp from the results file
#         last_written_timestamp = get_last_written_timestamp()

#         # Check if the current timestamp exceeds the last written timestamp by more than 5 minutes
#         if last_written_timestamp and (current_timestamp - last_written_timestamp) > timedelta(minutes=5):
#             print(f"Time gap exceeded 5 minutes. Restarting from checkpoint...")  # Debug print
#             save_checkpoint(i, key, total_elapsed_time, last_written_timestamp)
#             # Restart the script
#             os.execv(sys.executable, ['python'] + sys.argv)
#             return  # Exit and let the program restart

#         for prompt_type in ["prompt_0shot", "prompt_5shot"]:
#             if prompt_type in data:
#                 prompt = data[prompt_type]
#                 golden_plan = data["golden_plan"]
#                 full_prompt = prefix_message + prompt + suffix_message

#                 max_retries = 3
#                 for retry in range(max_retries):
#                     try:
#                         # Set a timeout for the prompt (5 minutes = 300 seconds)
#                         try:
#                             response = await asyncio.wait_for(ai.chat_round_str(full_prompt), timeout=300)
#                         except asyncio.TimeoutError:
#                             print(f"Prompt {key} timed out after 5 minutes. Skipping...")  # Debug print
#                             continue  # Skip this prompt and move to the next one

#                         # Extract the code from the response
#                         code = extract_code(response)
#                         if code:
#                             # Run the generated code
#                             code_output, error_type = run_generated_code(code)
#                             if code_output:
#                                 predicted_time = code_output
#                             else:
#                                 predicted_time = None
#                         else:
#                             predicted_time = None
#                             error_type = "NoCodeGenerated"

#                         expected_time = convert_golden_plan(golden_plan)

#                         # Append results based on prompt type.
#                         if prompt_type == "prompt_0shot":
#                             expected_outputs_0shot.append(expected_time)
#                             predicted_outputs_0shot.append(predicted_time)
#                             if error_type is None:
#                                 no_error_count_0shot += 1
#                                 if predicted_time == expected_time:
#                                     correct_output_count_0shot += 1
#                         elif prompt_type == "prompt_5shot":
#                             expected_outputs_5shot.append(expected_time)
#                             predicted_outputs_5shot.append(predicted_time)
#                             if error_type is None:
#                                 no_error_count_5shot += 1
#                                 if predicted_time == expected_time:
#                                     correct_output_count_5shot += 1

#                         timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
#                         line = (
#                             f"\n{key}. [{timestamp}] | PROMPT TYPE: {prompt_type} | ANSWER: {predicted_time} "
#                             f"EXPECTED: {expected_time} | ERROR: {error_type}\n"
#                         )
#                         print(line)  # Debug print

#                         with open("DS-R1-DL-8B_json_results.txt", "a") as file:
#                             file.write(line)

#                         # Construct JSON output manually.
#                         json_output = {
#                             "final_program_time": predicted_time,
#                             "expected_time": expected_time,
#                             "type_error": error_type,
#                             "full_response": response,
#                             "count": key  # Use the key (e.g., "calendar_scheduling_0") as the count
#                         }

#                         # Append JSON output to the appropriate section in the JSON file.
#                         with open("DS-R1-DL-8B_jsoncode_results.json", "r+") as json_file:
#                             file_data = json.load(json_file)
#                             if prompt_type == "prompt_0shot":
#                                 file_data["0shot"].append(json_output)
#                             elif prompt_type == "prompt_5shot":
#                                 file_data["5shot"].append(json_output)
#                             json_file.seek(0)
#                             json.dump(file_data, json_file, indent=4)
#                             json_file.truncate()

#                         # Update the last written timestamp
#                         last_written_timestamp = timestamp
#                         save_checkpoint(i + 1, key, total_elapsed_time, last_written_timestamp)

#                         break  # Exit retry loop if successful

#                     except RuntimeError as e:
#                         print(f"Error occurred (retry {retry + 1}/{max_retries}): {e}")  # Debug print
#                         if retry == max_retries - 1:
#                             print("Max retries reached. Skipping this prompt.")  # Debug print
#                             break
#                     except Exception as e:
#                         print(f"Unexpected error occurred: {e}")  # Debug print
#                         break  # Exit retry loop on unexpected errors

#                 # Restart the model every 5 prompts.
#                 if (i + 1) % 5 == 0:
#                     torch.cuda.empty_cache()
#                     ai = restart_model(engine)

#     end_time_value = datetime.now()
#     current_session_time = (end_time_value - start_time_value).total_seconds()
#     total_elapsed_time += current_session_time  # Add current session time to total elapsed time

#     # Calculate accuracies.
#     accuracy_0shot = calculate_accuracy(expected_outputs_0shot, predicted_outputs_0shot)
#     accuracy_5shot = calculate_accuracy(expected_outputs_5shot, predicted_outputs_5shot)
#     total_accuracy = calculate_accuracy(
#         expected_outputs_0shot + expected_outputs_5shot,
#         predicted_outputs_0shot + predicted_outputs_5shot,
#     )

#     # Calculate accuracy for programs that had no error
#     no_error_accuracy_0shot = (correct_output_count_0shot / no_error_count_0shot) * 100 if no_error_count_0shot > 0 else 0
#     no_error_accuracy_5shot = (correct_output_count_5shot / no_error_count_5shot) * 100 if no_error_count_5shot > 0 else 0

#     accuracy_line = (
#         f"\n0-shot prompts: Model guessed {sum(1 for exp, pred in zip(expected_outputs_0shot, predicted_outputs_0shot) if exp == pred)} out of {len(expected_outputs_0shot)} correctly.\n"
#         f"Accuracy: {accuracy_0shot:.2f}%\n"
#         f"\n5-shot prompts: Model guessed {sum(1 for exp, pred in zip(expected_outputs_5shot, predicted_outputs_5shot) if exp == pred)} out of {len(expected_outputs_5shot)} correctly.\n"
#         f"Accuracy: {accuracy_5shot:.2f}%\n"
#         f"\nTotal accuracy: {total_accuracy:.2f}%\n"
#         f"\n0-shot prompts with no errors: {correct_output_count_0shot} out of {no_error_count_0shot} produced correct outputs.\n"
#         f"No-error accuracy: {no_error_accuracy_0shot:.2f}%\n"
#         f"\n5-shot prompts with no errors: {correct_output_count_5shot} out of {no_error_count_5shot} produced correct outputs.\n"
#         f"No-error accuracy: {no_error_accuracy_5shot:.2f}%\n"
#         f"\nTotal time taken: {total_elapsed_time} seconds"
#     )

#     with open("DS-R1-DL-8B_json_results.txt", "a") as file:
#         file.write(accuracy_line)

# # Run the model.
# if __name__ == "__main__":
#     while True:
#         asyncio.run(run_model())








