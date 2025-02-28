#*****************WORKING JSON FORCE CODE (TEXT OUTPUTS)*************************************

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

# Define the JSON schema for the time range output
JSON_SCHEMA = {
    "type": "object",
    "properties": {
        "time_range": {
            "type": "string",
            "pattern": "^\\{\\d{2}:\\d{2}:\\d{2}:\\d{2}\\}$"
        }
    },
    "required": ["time_range"],
}

# Load the calendar scheduling examples from the JSON file
with open('test_scheduling.json', 'r') as file:
    calendar_examples = json.load(file)

# Argument parser to select the model
parser = argparse.ArgumentParser(description="Select a HuggingFace model.")
parser.add_argument('--model', type=str, required=True, help="The HuggingFace model ID to use.")
args = parser.parse_args()

# Load the model selected by the user
class JSONGuidanceHFWrapper(WrapperEngine):
    def __init__(self, engine: HuggingEngine, *args, json_schema, **kwargs):
        super().__init__(engine, *args, **kwargs)
        # keep a reference to the JSON schema we want to use
        self.engine: HuggingEngine  # type hint for IDEs
        self.json_schema = json_schema
        self.outlines_tokenizer = outlines.models.TransformerTokenizer(self.engine.tokenizer)

    def _create_logits_processor(self):
        json_logits_processor = outlines.processors.JSONLogitsProcessor(self.json_schema, self.outlines_tokenizer)
        return transformers.LogitsProcessorList([json_logits_processor])

    async def predict(self, *args, **kwargs):
        # each time we call predict or stream, pass a new instance of JSONLogitsProcessor
        if "logits_processor" not in kwargs:
            kwargs["logits_processor"] = self._create_logits_processor()
        return await super().predict(*args, **kwargs)

    async def stream(self, *args, **kwargs):
        # each time we call predict or stream, pass a new instance of JSONLogitsProcessor
        if "logits_processor" not in kwargs:
            kwargs["logits_processor"] = self._create_logits_processor()
        async for elem in super().stream(*args, **kwargs):
            yield elem

model = HuggingEngine(model_id=args.model)
engine = JSONGuidanceHFWrapper(model, json_schema=JSON_SCHEMA)

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

# Initialize lists to store 0-shot and 5-shot results
results_0shot = []
results_5shot = []

# Open the text file for writing results
with open('ML-ML-3.1-8B_text_txtresults.txt', 'w') as txt_file, open('ML-ML-3.1-8B_json_txtresults.json', 'w') as json_file:
    start_time = datetime.datetime.now()
    
    for example_id, example in calendar_examples.items():
        for prompt_type in ['prompt_0shot', 'prompt_5shot']:
            prompt = example[prompt_type]
            golden_plan = example['golden_plan']

            # Parse golden plan into {HH:MM:HH:MM} format
            expected_time = parse_golden_plan_time(golden_plan)

            # Append the suffix to the prompt
            prompt += "\n\nPlease output the proposed time in the following JSON format:\n{\"time_range\": \"{HH:MM:HH:MM}\"}. For example, if the proposed time is 14:30 to 15:30, the output should be:\n{\"time_range\": \"{14:30:15:30}\"}"

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
            
            def validate_time_range(time_range):
                """Validate that the time range matches the expected format."""
                return re.match(r'^\{\d{1,2}:\d{2}:\d{1,2}:\d{2}\}$', time_range) is not None

            if model_response:
                model_time = extract_time_range(model_response)
                if not validate_time_range(model_time):
                    model_time = "Invalid response"
            else:
                model_time = "Invalid response"     
                   
            # Print the formatted output to the terminal
            timestamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            print(f"{example_id}. [{timestamp}] | PROMPT TYPE: {prompt_type} | ANSWER: {model_time} EXPECTED: {expected_time}")

            # Write to the text file immediately
            txt_file.write(f"{example_id}. [{timestamp}] | PROMPT TYPE: {prompt_type} | ANSWER: {model_time} EXPECTED: {expected_time}\n")
            
            # Prepare the JSON output
            result_entry = {
                "final_time": f"{model_time}",
                "expected_time": f"{expected_time}",
                "exact_response": model_response,
                "count": example_id
            }
            
            # Append the result to the appropriate list
            if prompt_type == 'prompt_0shot':
                results_0shot.append(result_entry)
            else:
                results_5shot.append(result_entry)
            
            # Clear the model_response and other temporary variables from memory
            del model_response, model_time, result_entry
            
    # Write the collected results to the JSON file in the desired format
    json.dump({
        "0shot": results_0shot,
        "5shot": results_5shot
    }, json_file, indent=4)
    
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

print("Processing complete. Results saved to model_results.txt and model_results.json.")


# import argparse
# import asyncio
# import json
# import datetime
# import outlines
# import transformers
# import re
# from kani import Kani
# from kani.engines.huggingface import HuggingEngine

# # Define the JSON schema for the time range output
# JSON_SCHEMA = {
#     "type": "object",
#     "properties": {
#         "time_range": {"type": "string"}
#     },
#     "required": ["time_range"]
# }

# # Load the calendar scheduling examples from the JSON file
# with open('100_prompt_scheduling.json', 'r') as file:
#     calendar_examples = json.load(file)

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
# # engine.hyperparams["logits_processor"] = transformers.LogitsProcessorList([json_logits_processor])

# # Create the Kani instance
# ai = Kani(engine)

# # Function to parse the golden plan time into {HH:MM:HH:MM} format
# def parse_golden_plan_time(golden_plan):
#     match = re.search(r'(\d{1,2}:\d{2}) - (\d{1,2}:\d{2})', golden_plan)
#     if match:
#         start_time, end_time = match.groups()
#         return f"{{{start_time}:{end_time}}}"
#     return "Invalid format"

# # Initialize counters for accuracy calculation
# correct_0shot = 0
# correct_5shot = 0
# total_0shot = 0
# total_5shot = 0

# # Open the text file for writing results
# with open('ML-ML-3.1-8B_text_txtresults.txt', 'w') as txt_file, open('ML-ML-3.1-8B_json_txtresults.json', 'w') as json_file:
#     start_time = datetime.datetime.now()
    
#     # Write the opening bracket for the JSON file (since it's an array of results)
#     json_file.write("[\n")
    
#     for example_id, example in calendar_examples.items():
#         for prompt_type in ['prompt_0shot', 'prompt_5shot']:
#             prompt = example[prompt_type]
#             golden_plan = example['golden_plan']

#             # Parse golden plan into {HH:MM:HH:MM} format
#             expected_time = parse_golden_plan_time(golden_plan)

#             # Append the suffix to the prompt
#             prompt += "\n\nPlease output the proposed time in the following JSON format:\n{\"time_range\": \"HH:MM:HH:MM\"}. Make sure not to use any Python code, just the JSON direct output."
            
#             # Run the model and capture the response
#             async def get_model_response():
#                 full_response = ""
#                 async for token in ai.chat_round_stream(prompt):
#                     full_response += token
#                     print(token, end="", flush=True)
#                 print()  # For a newline after the response
#                 return full_response.strip()  # Return the actual response
            
#             model_response = asyncio.run(get_model_response())

#             def extract_time_range(response):
#                 """Extracts HH:MM:HH:MM format from the model's raw response and removes leading zeros from single-digit hours."""
#                 if not response or not isinstance(response, str):  # Check if response is None or not a string
#                     return "Invalid response"
                
#                 # Extract the time range using regex
#                 match = re.search(r'(\d{1,2}:\d{2}):(\d{1,2}:\d{2})', response)
#                 if not match:
#                     return "Invalid response"
                
#                 # Remove leading zeros from single-digit hours
#                 start_time = match.group(1)
#                 end_time = match.group(2)
                
#                 # Function to remove leading zeros from single-digit hours
#                 def remove_leading_zero(time_str):
#                     parts = time_str.split(':')
#                     hour = parts[0].lstrip('0')  # Remove leading zeros from the hour
#                     return f"{hour}:{parts[1]}"
                
#                 start_time = remove_leading_zero(start_time)
#                 end_time = remove_leading_zero(end_time)
                
#                 return f"{{{start_time}:{end_time}}}"

#             # Extract the time range from the model's response
#             if model_response:
#                 model_time = extract_time_range(model_response)
#             else:
#                 model_time = "Invalid response"     
                   
#             # Print the formatted output to the terminal
#             timestamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
#             print(f"{example_id}. [{timestamp}] | PROMPT TYPE: {prompt_type} | ANSWER: {model_time} EXPECTED: {expected_time}")

#             # Write to the text file immediately
#             txt_file.write(f"{example_id}. [{timestamp}] | PROMPT TYPE: {prompt_type} | ANSWER: {model_time} EXPECTED: {expected_time}\n")
            
#             # Prepare the JSON output
#             result_entry = {
#                 "final_time": f"{model_time}",
#                 "expected_time": f"{expected_time}",
#                 "exact_response": model_response,
#                 "count": example_id
#             }
            
#             # Write the JSON result immediately (one line per result)
#             json.dump(result_entry, json_file)
#             json_file.write(",\n")  # Add a comma and newline for the next entry
            
#             # Update counters
#             if prompt_type == 'prompt_0shot':
#                 total_0shot += 1
#                 if model_time == expected_time:
#                     correct_0shot += 1
#             else:
#                 total_5shot += 1
#                 if model_time == expected_time:
#                     correct_5shot += 1
            
#             # Clear the model_response and other temporary variables from memory
#             del model_response, model_time, result_entry
            
#     # Write the closing bracket for the JSON file
#     json_file.write("]\n")
    
#     # Calculate accuracies
#     accuracy_0shot = (correct_0shot / total_0shot) * 100 if total_0shot > 0 else 0
#     accuracy_5shot = (correct_5shot / total_5shot) * 100 if total_5shot > 0 else 0
#     total_accuracy = ((correct_0shot + correct_5shot) / (total_0shot + total_5shot)) * 100 if (total_0shot + total_5shot) > 0 else 0
    
#     # Write the final accuracy to the text file
#     end_time = datetime.datetime.now()
#     total_time = end_time - start_time
#     txt_file.write(f"\n0-shot prompts: Model guessed {correct_0shot} out of {total_0shot} correctly.\n")
#     txt_file.write(f"Accuracy: {accuracy_0shot:.2f}%\n")
#     txt_file.write(f"5-shot prompts: Model guessed {correct_5shot} out of {total_5shot} correctly.\n")
#     txt_file.write(f"Accuracy: {accuracy_5shot:.2f}%\n")
#     txt_file.write(f"Total accuracy: {total_accuracy:.2f}%\n")
#     txt_file.write(f"Total time taken: {total_time}\n")

# print("Processing complete. Results saved to model_results.txt and model_results.json.")


# import argparse
# import asyncio
# import json
# import datetime
# import outlines
# import transformers
# import re
# from kani import Kani
# from kani.engines.huggingface import HuggingEngine

# # Define the JSON schema for the time range output
# JSON_SCHEMA = {
#     "type": "object",
#     "properties": {
#         "time_range": {"type": "string"}
#     },
#     "required": ["time_range"]
# }

# # Load the calendar scheduling examples from the JSON file
# with open('100_prompt_scheduling.json', 'r') as file:
#     calendar_examples = json.load(file)

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
# # engine.hyperparams["logits_processor"] = transformers.LogitsProcessorList([json_logits_processor])

# # Create the Kani instance
# ai = Kani(engine)

# # Function to parse the golden plan time into {HH:MM:HH:MM} format
# def parse_golden_plan_time(golden_plan):
#     match = re.search(r'(\d{1,2}:\d{2}) - (\d{1,2}:\d{2})', golden_plan)
#     if match:
#         start_time, end_time = match.groups()
#         return f"{{{start_time}:{end_time}}}"
#     return "Invalid format"

# # Initialize counters for accuracy calculation
# correct_0shot = 0
# correct_5shot = 0
# total_0shot = 0
# total_5shot = 0

# # Initialize lists for JSON output
# results_0shot = []
# results_5shot = []

# # Open the text file for writing results
# with open('ML-ML-3.1-8B_text_txtresults.txt', 'w') as txt_file, open('ML-ML-3.1-8B_json_txtresults.json', 'w') as json_file:
#     start_time = datetime.datetime.now()
    
#     for example_id, example in calendar_examples.items():
#         for prompt_type in ['prompt_0shot', 'prompt_5shot']:
#             prompt = example[prompt_type]
#             golden_plan = example['golden_plan']

#             # Parse golden plan into {HH:MM:HH:MM} format
#             expected_time = parse_golden_plan_time(golden_plan)

#             # Append the suffix to the prompt
#             prompt += "\n\nPlease output the proposed time in the following JSON format:\n{\"time_range\": \"HH:MM:HH:MM\"}. Make sure not to use any Python code, just the JSON direct output."
            
#             # Run the model and capture the response
#             async def get_model_response():
#                 full_response = ""
#                 async for token in ai.chat_round_stream(prompt):
#                     full_response += token
#                     print(token, end="", flush=True)
#                 print()  # For a newline after the response
#                 return full_response.strip()  # Return the actual response
            
#             model_response = asyncio.run(get_model_response())

#             def extract_time_range(response):
#                 """Extracts HH:MM:HH:MM format from the model's raw response and removes leading zeros from single-digit hours."""
#                 if not response or not isinstance(response, str):  # Check if response is None or not a string
#                     return "Invalid response"
                
#                 # Extract the time range using regex
#                 match = re.search(r'(\d{1,2}:\d{2}):(\d{1,2}:\d{2})', response)
#                 if not match:
#                     return "Invalid response"
                
#                 # Remove leading zeros from single-digit hours
#                 start_time = match.group(1)
#                 end_time = match.group(2)
                
#                 # Function to remove leading zeros from single-digit hours
#                 def remove_leading_zero(time_str):
#                     parts = time_str.split(':')
#                     hour = parts[0].lstrip('0')  # Remove leading zeros from the hour
#                     return f"{hour}:{parts[1]}"
                
#                 start_time = remove_leading_zero(start_time)
#                 end_time = remove_leading_zero(end_time)
                
#                 return f"{{{start_time}:{end_time}}}"

#             # Extract the time range from the model's response
#             if model_response:
#                 model_time = extract_time_range(model_response)
#             else:
#                 model_time = "Invalid response"     
                   
#             # Print the formatted output to the terminal
#             timestamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
#             print(f"{example_id}. [{timestamp}] | PROMPT TYPE: {prompt_type} | ANSWER: {model_time} EXPECTED: {expected_time}")

#             # Write to the text file
#             txt_file.write(f"{example_id}. [{timestamp}] | PROMPT TYPE: {prompt_type} | ANSWER: {model_time} EXPECTED: {expected_time}\n")
            
#             # Prepare the JSON output
#             result_entry = {
#                 "final_time": f"{model_time}",
#                 "expected_time": f"{expected_time}",
#                 "exact_response": model_response,
#                 "count": example_id
#             }
            
#             if prompt_type == 'prompt_0shot':
#                 results_0shot.append(result_entry)
#                 total_0shot += 1
#                 if model_time == expected_time:
#                     correct_0shot += 1
#             else:
#                 results_5shot.append(result_entry)
#                 total_5shot += 1
#                 if model_time == expected_time:
#                     correct_5shot += 1
    
#     # Calculate accuracies
#     accuracy_0shot = (correct_0shot / total_0shot) * 100 if total_0shot > 0 else 0
#     accuracy_5shot = (correct_5shot / total_5shot) * 100 if total_5shot > 0 else 0
#     total_accuracy = ((correct_0shot + correct_5shot) / (total_0shot + total_5shot)) * 100 if (total_0shot + total_5shot) > 0 else 0
    
#     # Write the final accuracy to the text file
#     end_time = datetime.datetime.now()
#     total_time = end_time - start_time
#     txt_file.write(f"\n0-shot prompts: Model guessed {correct_0shot} out of {total_0shot} correctly.\n")
#     txt_file.write(f"Accuracy: {accuracy_0shot:.2f}%\n")
#     txt_file.write(f"5-shot prompts: Model guessed {correct_5shot} out of {total_5shot} correctly.\n")
#     txt_file.write(f"Accuracy: {accuracy_5shot:.2f}%\n")
#     txt_file.write(f"Total accuracy: {total_accuracy:.2f}%\n")
#     txt_file.write(f"Total time taken: {total_time}\n")
    
#     # Write the JSON output
#     json_output = {
#         "0shot": results_0shot,
#         "5shot": results_5shot
#     }
#     json.dump(json_output, json_file, indent=4)

# print("Processing complete. Results saved to model_results.txt and model_results.json.")


#*****NEW FULLY WORKING CODE*****

# import json
# import asyncio
# import logging
# import os
# from argparse import ArgumentParser
# from datetime import datetime
# import torch
# import outlines
# import transformers
# from kani import Kani
# from kani.engines.huggingface import HuggingEngine

# # Configure logging
# logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')

# # Define a JSON schema for the forced JSON output.
# JSON_SCHEMA = {
#     "type": "object",
#     "properties": {
#         "time_range": {
#             "type": "string",
#             "pattern": "^\\{\\d{2}:\\d{2}:\\d{2}:\\d{2}\\}$"
#         }
#     },
#     "required": ["time_range"],
# }

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
#     "\nProvide your answer as a JSON object exactly in the following format:\n"
#     '{"time_range": "{HH:MM:HH:MM}"}\n'
#     "Do not include any extra words, explanations, or other text."
#     'Here is an example of an output: {"time_range": "{14:30:15:30}".'
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

# # Helper function to normalize time format (only remove leading zeros from the hour part)
# def normalize_time_format(time_str):
#     if time_str and time_str.startswith("{") and time_str.endswith("}"):
#         time_str = time_str[1:-1]  # Remove the curly braces
#         parts = time_str.split(":")
#         if len(parts) >= 2:  # Ensure there are at least hours and minutes
#             # Normalize only the hour part (first part)
#             hour_part = parts[0]
#             normalized_hour = str(int(hour_part))  # Remove leading zeros
#             # Reconstruct the time string with normalized hour
#             normalized_time = f"{{{normalized_hour}:{':'.join(parts[1:])}}}"
#             return normalized_time
#     return time_str  # Return the original string if it doesn't match the expected format

# # Function to parse the model’s JSON response.
# def extract_time_from_json(response):
#     try:
#         data = json.loads(response)
#         time_range = data.get("time_range")
#         if time_range and not time_range.startswith("{"):
#             time_range = f"{{{time_range}}}"
#         time_range = normalize_time_format(time_range)  # Normalize the time format
#         print(f"Extracted time: {time_range}")  # Debug print
#         return time_range
#     except json.JSONDecodeError:
#         start = response.find("{")
#         end = response.rfind("}")
#         if start != -1 and end != -1:
#             try:
#                 data = json.loads(response[start : end + 1])
#                 time_range = data.get("time_range")
#                 if time_range and not time_range.startswith("{"):
#                     time_range = f"{{{time_range}}}"
#                 time_range = normalize_time_format(time_range)  # Normalize the time format
#                 print(f"Extracted time from substring: {time_range}")  # Debug print
#                 return time_range
#             except Exception:
#                 print("Failed to extract time from substring.")  # Debug print
#                 return None
#         else:
#             print("No valid JSON substring found.")  # Debug print
#             return None

# # Function to convert the golden plan to dictionary format and remove days of the week.
# def convert_golden_plan(golden_plan):
#     if "Here is the proposed time:" in golden_plan:
#         time_part = golden_plan.split(": ")[-1].strip()
#         start_time, end_time = time_part.split(" - ")
#         start_time = start_time.split(", ")[-1] if ", " in start_time else start_time
#         end_time = end_time.split(", ")[-1] if ", " in end_time else end_time
#         time_range = f"{{{start_time}:{end_time}}}"
#         return normalize_time_format(time_range)  # Normalize the time format
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
# def save_checkpoint(index, count):
#     try:
#         with open("checkpoint.txt", "w") as file:
#             file.write(f"{index},{count}")
#     except Exception as e:
#         print(f"Failed to save checkpoint: {e}")  # Debug print

# # Function to load checkpoint and current count.
# def load_checkpoint():
#     if os.path.exists("checkpoint.txt"):
#         try:
#             with open("checkpoint.txt", "r") as file:
#                 index, count = file.read().strip().split(",")
#                 print(f"Loaded checkpoint: index={index}, count={count}")  # Debug print
#                 return int(index), int(count)
#         except Exception as e:
#             print(f"Failed to load checkpoint: {e}")  # Debug print
#     return 0, 0

# # Main function to run the model.
# async def run_model():
#     expected_outputs_0shot = []
#     predicted_outputs_0shot = []
#     expected_outputs_5shot = []
#     predicted_outputs_5shot = []
#     start_time_value = datetime.now()

#     # Load checkpoint (index, count)
#     start_index, count = load_checkpoint()

#     # Initialize text results file if it doesn't exist.
#     if not os.path.exists("DS-R1-DL-70B_text_results.txt"):
#         print("Initializing text results file...")  # Debug print
#         with open("DS-R1-DL-70B_text_results.txt", "w") as file:
#             file.write("Model Results:\n")

#     # Initialize JSON results file if it doesn't exist.
#     if not os.path.exists("DS-R1-DL-70B_json_results.json"):
#         print("Initializing JSON results file...")  # Debug print
#         with open("DS-R1-DL-70B_json_results.json", "w") as json_file:
#             json.dump({"0shot": [], "5shot": []}, json_file)

#     prompts_data = load_prompts("100_prompt_scheduling.json")
#     prompts_list = list(prompts_data.items())

#     engine = initialize_engine(args.model)
#     ai = Kani(engine)

#     for i in range(start_index, len(prompts_list)):
#         key, data = prompts_list[i]

#         for prompt_type in ["prompt_0shot", "prompt_5shot"]:
#             if prompt_type in data:
#                 prompt = data[prompt_type]
#                 golden_plan = data["golden_plan"]
#                 full_prompt = prefix_message + prompt + suffix_message

#                 max_retries = 3
#                 for retry in range(max_retries):
#                     try:
#                         # Get the full JSON response from the model.
#                         response = await ai.chat_round_str(full_prompt)

#                         predicted_time = extract_time_from_json(response)
#                         expected_time = convert_golden_plan(golden_plan)

#                         if predicted_time is None:
#                             print(f"No valid time found in JSON response for {prompt_type} in {key}")  # Debug print
#                             continue  # Skip if no valid time found

#                         # Append results based on prompt type.
#                         if prompt_type == "prompt_0shot":
#                             expected_outputs_0shot.append(expected_time)
#                             predicted_outputs_0shot.append(predicted_time)
#                         elif prompt_type == "prompt_5shot":
#                             expected_outputs_5shot.append(expected_time)
#                             predicted_outputs_5shot.append(predicted_time)

#                         timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
#                         line = (
#                             f"\n{key}. [{timestamp}] | PROMPT TYPE: {prompt_type} | ANSWER: {predicted_time} "
#                             f"EXPECTED: {expected_time}\n"
#                         )
#                         print(line)  # Debug print

#                         with open("DS-R1-DL-70B_text_results.txt", "a") as file:
#                             file.write(line)

#                         # Construct JSON output manually.
#                         json_output = {
#                             "final_time": predicted_time,
#                             "expected_time": expected_time,
#                             "exact_response": response,
#                             "count": key,
#                         }

#                         # Append JSON output to the appropriate section in the JSON file.
#                         with open("DS-R1-DL-70B_json_results.json", "r+") as json_file:
#                             file_data = json.load(json_file)
#                             if prompt_type == "prompt_0shot":
#                                 file_data["0shot"].append(json_output)
#                             elif prompt_type == "prompt_5shot":
#                                 file_data["5shot"].append(json_output)
#                             json_file.seek(0)
#                             json.dump(file_data, json_file, indent=4)
#                             json_file.truncate()

#                         count += 1  # Increment the count
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
#                 if count % 5 == 0:
#                     torch.cuda.empty_cache()
#                     ai = restart_model(engine)

#         # Save checkpoint after each prompt.
#         save_checkpoint(i + 1, count)

#     end_time_value = datetime.now()
#     total_time = end_time_value - start_time_value

#     # Calculate accuracies.
#     accuracy_0shot = calculate_accuracy(expected_outputs_0shot, predicted_outputs_0shot)
#     accuracy_5shot = calculate_accuracy(expected_outputs_5shot, predicted_outputs_5shot)
#     total_accuracy = calculate_accuracy(
#         expected_outputs_0shot + expected_outputs_5shot,
#         predicted_outputs_0shot + predicted_outputs_5shot,
#     )

#     accuracy_line = (
#         f"\n0-shot prompts: Model guessed {sum(1 for exp, pred in zip(expected_outputs_0shot, predicted_outputs_0shot) if exp == pred)} out of {len(expected_outputs_0shot)} correctly.\n"
#         f"Accuracy: {accuracy_0shot:.2f}%\n"
#         f"\n5-shot prompts: Model guessed {sum(1 for exp, pred in zip(expected_outputs_5shot, predicted_outputs_5shot) if exp == pred)} out of {len(expected_outputs_5shot)} correctly.\n"
#         f"Accuracy: {accuracy_5shot:.2f}%\n"
#         f"\nTotal accuracy: {total_accuracy:.2f}%\n"
#         f"\nTotal time taken: {total_time}"
#     )

#     with open("DS-R1-DL-70B_text_results.txt", "a") as file:
#         file.write(accuracy_line)

# # Run the model.
# if __name__ == "__main__":
#     asyncio.run(run_model())


#***************************NOT WORKING*******************************

# import os
# import json
# from kani import Kani
# from kani.engines.huggingface import HuggingEngine
# import asyncio
# from argparse import ArgumentParser
# from datetime import datetime
# import torch  # For clearing GPU cache


# # Argument parser for model selection
# parser = ArgumentParser()
# parser.add_argument("--model", dest="model", help="Model name to use")
# args = parser.parse_args()


# # Load the prompts from the JSON file
# with open("test_scheduling.json", "r") as file:
#    prompts_data = json.load(file)


# # Define prefix and suffix messages
# prefix_message = "You are an expert at scheduling meetings. Your task is to find a suitable time for a meeting based on the participants' schedules and constraints. Follow these rules:\n"
# suffix_message = "\nProvide the meeting time range in the exact format {HH:MM:HH:MM}. Do not include any extra words, explanations, or other text. Only return the response in this format. Example output: {14:30:15:30}."


# # Initialize the model
# engine = HuggingEngine(
#    model_id=args.model,
#    use_auth_token=True,
#    model_load_kwargs={
#        "device_map": "auto",
#        "trust_remote_code": True,
#        "pad_token_id": 128001,  # Explicitly set pad_token_id to suppress warnings
#    },
# )
# ai = Kani(engine)


# # Function to extract the time from the model's response
# def extract_time(response):
#    start = response.find("{")
#    end = response.find("}")
#    if start != -1 and end != -1:
#        time_str = response[start:end+1]
#        return time_str
#    return None


# # Function to convert the golden plan to dictionary format and remove days of the week
# def convert_golden_plan(golden_plan):
#    if "Here is the proposed time:" in golden_plan:
#        time_part = golden_plan.split(": ")[-1].strip()
#        start_time, end_time = time_part.split(" - ")
#        start_time = start_time.split(", ")[-1] if ", " in start_time else start_time
#        end_time = end_time.split(", ")[-1] if ", " in end_time else end_time
#        return f"{{{start_time}:{end_time}}}"
#    return None


# # Function to calculate accuracy
# def calculate_accuracy(expected, predicted):
#    correct = 0
#    for exp, pred in zip(expected, predicted):
#        if exp == pred:
#            correct += 1
#    return (correct / len(expected)) * 100 if expected else 0


# # Function to restart the model
# def restart_model():
#    global ai
#    del ai
#    torch.cuda.empty_cache()  # Clear GPU cache
#    ai = Kani(engine)  # Reinitialize the model


# # Function to save checkpoint and current count
# def save_checkpoint(index, count):
#    with open("checkpoint.txt", "w") as file:
#        file.write(f"{index},{count}")


# # Function to load checkpoint and current count
# def load_checkpoint():
#    if os.path.exists("checkpoint.txt"):
#        with open("checkpoint.txt", "r") as file:
#            index, count = file.read().strip().split(",")
#            return int(index), int(count)  # Ensure count continues correctly
#    return 0, 0  # Start from 0 index and count 0 if no checkpoint exists


# # Main function to run the model
# async def run_model():
#    expected_outputs_0shot = []
#    predicted_outputs_0shot = []
#    expected_outputs_5shot = []
#    predicted_outputs_5shot = []
#    start_time = datetime.now()


#    # Load checkpoint (index, count)
#    start_index, count = load_checkpoint()


#    # Initialize text results file if it doesn't exist
#    if not os.path.exists("DS-R1-DL-70B_text_results.txt"):
#        with open("DS-R1-DL-70B_text_results.txt", "w") as file:
#            file.write("Model Results:\n")


#    # Initialize JSON results file if it doesn't exist
#    if not os.path.exists("DS-R1-DL-70B_json_results.json"):
#        with open("DS-R1-DL-70B_json_results.json", "w") as json_file:
#            json.dump({"0shot": [], "5shot": []}, json_file)  # Initialize with empty arrays for 0-shot and 5-shot


#    prompts_list = list(prompts_data.items())


#    for i in range(start_index, len(prompts_list)):
#        key, data = prompts_list[i]
#        # prompt_types = [k for k in data.keys() if k.startswith("prompt_")]


#        for prompt_type in ['prompt_0shot', 'prompt_5shot']:
#            if prompt_type in data:
#                prompt = data[prompt_type]
#                golden_plan = data["golden_plan"]


#                full_prompt = prefix_message + prompt + suffix_message
#                print(f"Processing {prompt_type} for {key}")  # Debugging


#            max_retries = 3
#            for retry in range(max_retries):
#                try:
#                    response = await ai.chat_round_str(full_prompt)
#                    predicted_time = extract_time(response)
#                    expected_time = convert_golden_plan(golden_plan)


#                    if predicted_time is None:
#                        print(f"Warning: No valid time found in response for {prompt_type} in {key}")
#                        continue  # Skip this prompt if no valid time is found


#                    # Append results based on prompt type
#                    if prompt_type == "prompt_0shot":
#                        expected_outputs_0shot.append(expected_time)
#                        predicted_outputs_0shot.append(predicted_time)
#                    elif prompt_type == "prompt_5shot":
#                        expected_outputs_5shot.append(expected_time)
#                        predicted_outputs_5shot.append(predicted_time)


#                    timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
#                    line = f"\n{key}. [{timestamp}] | PROMPT TYPE: {prompt_type} | ANSWER: {predicted_time} EXPECTED: {expected_time}\n"
#                    print(line)


#                    with open("DS-R1-DL-70B_text_results.txt", "a") as file:
#                        file.write(line)


#                    # Construct JSON output manually
#                    json_output = {
#                        "final_time": predicted_time,
#                        "expected_time": expected_time,
#                        "exact_response": response,
#                        "count": key
#                    }


#                    # Append JSON output to the appropriate section in the JSON file
#                    with open("DS-R1-DL-70B_json_results.json", "r+") as json_file:
#                        data = json.load(json_file)
#                        if prompt_type == "prompt_0shot":
#                            data["0shot"].append(json_output)
#                        elif prompt_type == "prompt_5shot":
#                            data["5shot"].append(json_output)
#                        json_file.seek(0)
#                        json.dump(data, json_file, indent=4)
#                        json_file.truncate()


#                    count += 1  # Increment the count
#                    break  # Exit retry loop if successful
#                except RuntimeError as e:
#                    print(f"Error occurred (retry {retry + 1}/{max_retries}): {e}")
#                    if retry == max_retries - 1:
#                        print("Max retries reached. Skipping this prompt.")
#                        break
#                except Exception as e:
#                    print(f"Unexpected error occurred: {e}")
#                    break  # Exit retry loop on unexpected errors


#            if count % 5 == 0:
#                torch.cuda.empty_cache()
#                restart_model()


#        # Save checkpoint and current count after each prompt
#        save_checkpoint(i + 1, count)


#    end_time = datetime.now()
#    total_time = end_time - start_time


#    # Calculate accuracy for 0-shot, 5-shot, and total
#    accuracy_0shot = calculate_accuracy(expected_outputs_0shot, predicted_outputs_0shot)
#    accuracy_5shot = calculate_accuracy(expected_outputs_5shot, predicted_outputs_5shot)
#    total_accuracy = calculate_accuracy(
#        expected_outputs_0shot + expected_outputs_5shot,
#        predicted_outputs_0shot + predicted_outputs_5shot,
#    )


#    accuracy_line = (
#        f"\n0-shot prompts: Model guessed {sum(1 for exp, pred in zip(expected_outputs_0shot, predicted_outputs_0shot) if exp == pred)} out of {len(expected_outputs_0shot)} prompts correctly.\nAccuracy: {accuracy_0shot:.2f}%\n"
#        f"\n5-shot prompts: Model guessed {sum(1 for exp, pred in zip(expected_outputs_5shot, predicted_outputs_5shot) if exp == pred)} out of {len(expected_outputs_5shot)} prompts correctly.\nAccuracy: {accuracy_5shot:.2f}%\n"
#        f"\nTotal accuracy: {total_accuracy:.2f}%\n"
#        f"\nTotal time taken: {total_time}"
#    )
#    print(accuracy_line)


#    with open("DS-R1-DL-70B_text_results.txt", "a") as file:
#        file.write(accuracy_line)


# # Run the model
# asyncio.run(run_model())




#*****OLD WORKING CODE*****

# import json
# import asyncio
# import logging
# import os
# from argparse import ArgumentParser
# from datetime import datetime
# import torch
# import outlines
# import transformers
# from kani import Kani
# from kani.engines.huggingface import HuggingEngine

# # Configure logging
# logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')

# # Define a JSON schema for the forced JSON output.
# JSON_SCHEMA = {
#     "type": "object",
#     "properties": {
#         "time_range": {
#             "type": "string",
#             "pattern": "^\\{\\d{2}:\\d{2}:\\d{2}:\\d{2}\\}$"
#         }
#     },
#     "required": ["time_range"],
# }

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
#     "\nProvide your answer as a JSON object exactly in the following format:\n"
#     '{"time_range": "{HH:MM:HH:MM}"}\n'
#     "Do not include any extra words, explanations, or other text."
#     'Here is an example of an output: {"time_range": "{14:30:15:30}".'
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

# # Function to parse the model’s JSON response.
# def extract_time_from_json(response):
#     try:
#         data = json.loads(response)
#         time_range = data.get("time_range")
#         if time_range and not time_range.startswith("{"):
#             time_range = f"{{{time_range}}}"
#         print(f"Extracted time: {time_range}")  # Debug print
#         return time_range
#     except json.JSONDecodeError:
#         start = response.find("{")
#         end = response.rfind("}")
#         if start != -1 and end != -1:
#             try:
#                 data = json.loads(response[start : end + 1])
#                 time_range = data.get("time_range")
#                 if time_range and not time_range.startswith("{"):
#                     time_range = f"{{{time_range}}}"
#                 print(f"Extracted time from substring: {time_range}")  # Debug print
#                 return time_range
#             except Exception:
#                 print("Failed to extract time from substring.")  # Debug print
#                 return None
#         else:
#             print("No valid JSON substring found.")  # Debug print
#             return None

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
# def save_checkpoint(index, count):
#     try:
#         with open("checkpoint.txt", "w") as file:
#             file.write(f"{index},{count}")
#     except Exception as e:
#         print(f"Failed to save checkpoint: {e}")  # Debug print

# # Function to load checkpoint and current count.
# def load_checkpoint():
#     if os.path.exists("checkpoint.txt"):
#         try:
#             with open("checkpoint.txt", "r") as file:
#                 index, count = file.read().strip().split(",")
#                 print(f"Loaded checkpoint: index={index}, count={count}")  # Debug print
#                 return int(index), int(count)
#         except Exception as e:
#             print(f"Failed to load checkpoint: {e}")  # Debug print
#     return 0, 0

# # Main function to run the model.
# async def run_model():
#     expected_outputs_0shot = []
#     predicted_outputs_0shot = []
#     expected_outputs_5shot = []
#     predicted_outputs_5shot = []
#     start_time_value = datetime.now()

#     # Load checkpoint (index, count)
#     start_index, count = load_checkpoint()

#     # Initialize text results file if it doesn't exist.
#     if not os.path.exists("ML-L-3.1-70B_text_results.txt"):
#         print("Initializing text results file...")  # Debug print
#         with open("ML-L-3.1-70B_text_results.txt", "w") as file:
#             file.write("Model Results:\n")

#     # Initialize JSON results file if it doesn't exist.
#     if not os.path.exists("ML-L-3.1-70B_json_results.json"):
#         print("Initializing JSON results file...")  # Debug print
#         with open("ML-L-3.1-70B_json_results.json", "w") as json_file:
#             json.dump({"0shot": [], "5shot": []}, json_file)

#     prompts_data = load_prompts("100_prompt_scheduling.json")
#     prompts_list = list(prompts_data.items())

#     engine = initialize_engine(args.model)
#     ai = Kani(engine)

#     for i in range(start_index, len(prompts_list)):
#         key, data = prompts_list[i]

#         for prompt_type in ["prompt_0shot", "prompt_5shot"]:
#             if prompt_type in data:
#                 prompt = data[prompt_type]
#                 golden_plan = data["golden_plan"]
#                 full_prompt = prefix_message + prompt + suffix_message

#                 max_retries = 3
#                 for retry in range(max_retries):
#                     try:
#                         # Get the full JSON response from the model.
#                         response = await ai.chat_round_str(full_prompt)

#                         predicted_time = extract_time_from_json(response)
#                         expected_time = convert_golden_plan(golden_plan)

#                         if predicted_time is None:
#                             print(f"No valid time found in JSON response for {prompt_type} in {key}")  # Debug print
#                             continue  # Skip if no valid time found

#                         # Append results based on prompt type.
#                         if prompt_type == "prompt_0shot":
#                             expected_outputs_0shot.append(expected_time)
#                             predicted_outputs_0shot.append(predicted_time)
#                         elif prompt_type == "prompt_5shot":
#                             expected_outputs_5shot.append(expected_time)
#                             predicted_outputs_5shot.append(predicted_time)

#                         timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
#                         line = (
#                             f"\n{key}. [{timestamp}] | PROMPT TYPE: {prompt_type} | ANSWER: {predicted_time} "
#                             f"EXPECTED: {expected_time}\n"
#                         )
#                         print(line)  # Debug print

#                         with open("ML-L-3.1-70B_text_results.txt", "a") as file:
#                             file.write(line)

#                         # Construct JSON output manually.
#                         json_output = {
#                             "final_time": predicted_time,
#                             "expected_time": expected_time,
#                             "exact_response": response,
#                             "count": key,
#                         }

#                         # Append JSON output to the appropriate section in the JSON file.
#                         with open("ML-L-3.1-70B_json_results.json", "r+") as json_file:
#                             file_data = json.load(json_file)
#                             if prompt_type == "prompt_0shot":
#                                 file_data["0shot"].append(json_output)
#                             elif prompt_type == "prompt_5shot":
#                                 file_data["5shot"].append(json_output)
#                             json_file.seek(0)
#                             json.dump(file_data, json_file, indent=4)
#                             json_file.truncate()

#                         count += 1  # Increment the count
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
#                 if count % 5 == 0:
#                     torch.cuda.empty_cache()
#                     ai = restart_model(engine)

#         # Save checkpoint after each prompt.
#         save_checkpoint(i + 1, count)

#     end_time_value = datetime.now()
#     total_time = end_time_value - start_time_value

#     # Calculate accuracies.
#     accuracy_0shot = calculate_accuracy(expected_outputs_0shot, predicted_outputs_0shot)
#     accuracy_5shot = calculate_accuracy(expected_outputs_5shot, predicted_outputs_5shot)
#     total_accuracy = calculate_accuracy(
#         expected_outputs_0shot + expected_outputs_5shot,
#         predicted_outputs_0shot + predicted_outputs_5shot,
#     )

#     accuracy_line = (
#         f"\n0-shot prompts: Model guessed {sum(1 for exp, pred in zip(expected_outputs_0shot, predicted_outputs_0shot) if exp == pred)} out of {len(expected_outputs_0shot)} correctly.\n"
#         f"Accuracy: {accuracy_0shot:.2f}%\n"
#         f"\n5-shot prompts: Model guessed {sum(1 for exp, pred in zip(expected_outputs_5shot, predicted_outputs_5shot) if exp == pred)} out of {len(expected_outputs_5shot)} correctly.\n"
#         f"Accuracy: {accuracy_5shot:.2f}%\n"
#         f"\nTotal accuracy: {total_accuracy:.2f}%\n"
#         f"\nTotal time taken: {total_time}"
#     )

#     with open("ML-L-3.1-70B_text_results.txt", "a") as file:
#         file.write(accuracy_line)

# # Run the model.
# if __name__ == "__main__":
#     asyncio.run(run_model())






