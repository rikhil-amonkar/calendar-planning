#******************************WORKING JSON FORCE CODE (CODE OUTPUTS)*************************************

import argparse
import asyncio
import json
import datetime
import outlines
import transformers
import re
import subprocess
from kani import Kani
from kani.engines.huggingface import HuggingEngine
from kani.engines import WrapperEngine

# Define the JSON schema for the output
JSON_SCHEMA = {
    "type": "object",
    "properties": {
        "explanation": {
            "type": "string"
        },
        "code": {
            "type": "string",
            "pattern": "^\"\"\\n'''python\\n([\\s\\S]+)\\n'''\\n\"\"\"$"
        }
    },
    "required": ["explanation", "code"]
}

# Load the calendar scheduling examples from the JSON file
with open('100_prompt_scheduling.json', 'r') as file:
    calendar_examples = json.load(file)

# Argument parser to select the model
parser = argparse.ArgumentParser(description="Select a HuggingFace model.")
parser.add_argument('--model', type=str, required=True, help="The HuggingFace model ID to use.")
args = parser.parse_args()

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

# Load the model selected by the user
model = HuggingEngine(model_id=args.model)
engine = JSONGuidanceHFWrapper(model, json_schema=JSON_SCHEMA)

# Create the Kani instance
ai = Kani(engine)

def extract_code(model_response):
    """Extract the code block from the model response."""
    match = re.search(r"'''python\n([\s\S]+?)\n'''", model_response)
    if match:
        return match.group(1)
    else:
        raise ValueError("Could not extract code from the model response.")

def write_code_to_file(code, filename="generated_code.py"):
    with open(filename, "w") as f:
        f.write(code)

def run_generated_code(filename="generated_code.py"):
    result = subprocess.run(["python", filename], capture_output=True, text=True)
    return result.stdout, result.stderr

def parse_output(output):
    """
    Parse the output to find the time in the format {HH:MM:HH:MM}.
    Remove leading zeros from single-digit hours.
    """
    match = re.search(r"\{(\d{2}:\d{2}:\d{2}:\d{2})\}", output)
    if match:
        time_str = match.group(0)
        return remove_leading_zero_from_hour(time_str)  # Remove leading zeros
    else:
        return None

def parse_golden_plan_time(golden_plan):
    """Parse the golden plan time into {HH:MM:HH:MM} format."""
    match = re.search(r'(\d{1,2}:\d{2}) - (\d{1,2}:\d{2})', golden_plan)
    if match:
        start_time, end_time = match.groups()
        return f"{{{start_time}:{end_time}}}"
    return "Invalid format"

def remove_leading_zero_from_hour(time_str):
    """
    Remove leading zeros from single-digit hours in a time string.
    Example: {09:30:10:30} → {9:30:10:30}
    """
    if not time_str or not isinstance(time_str, str):
        return time_str  # Return as-is if invalid input

    # Use regex to find and remove leading zeros from single-digit hours
    def remove_zero(match):
        hour = match.group(1).lstrip('0')  # Remove leading zeros
        return f"{hour}:{match.group(2)}"

    # Apply the function to all occurrences of HH:MM
    time_str = re.sub(r"(\d{2}):(\d{2})", remove_zero, time_str)
    return time_str

def categorize_error(error_message):
    if "SyntaxError" in error_message:
        return "SyntaxError"
    elif "IndentationError" in error_message:
        return "IndentationError"
    elif "NameError" in error_message:
        return "NameError"
    elif "TypeError" in error_message:
        return "TypeError"
    elif "ValueError" in error_message:
        return "ValueError"
    elif "ImportError" in error_message:
        return "ImportError"
    elif "RuntimeError" in error_message:
        return "RuntimeError"
    else:
        return "Other"

# Initialize counters for accuracy calculation
correct_0shot = 0
correct_5shot = 0
total_0shot = 0
total_5shot = 0
no_error_0shot = 0
no_error_5shot = 0

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
            prompt += "\n\nPlease generate a full Python script program which calculates the proposed time. " \
                      "Ensure the code is clean, well-formatted, and free from unnecessary escape characters or tags. " \
                      "Generate a response in the following JSON format. Ensure the code starts with '''python and ends with ''' to encase the code. Use proper indentation and spacing. " \
                      "Finally, make sure the output of the program you generate displays the calculated time in the following format: {HH:MM:HH:MM}. " \
                      "Here is an example of a possible format of time: {14:30:15:30}. " \
                      "The final time must be encased in curly brackets: {}. " \
                      "Generate a response in the following JSON format. Ensure the response strictly adheres to the JSON schema and does not include any additional text outside the JSON structure."

            # Run the model and capture the response
            async def get_model_response():
                full_response = ""
                async for token in ai.chat_round_stream(prompt):
                    full_response += token
                    print(token, end="", flush=True)
                print()  # For a newline after the response
                return full_response.strip()  # Return the actual response
            
            model_response = asyncio.run(get_model_response())

            # Extract the code from the model response
            try:
                code = extract_code(model_response)
                write_code_to_file(code)
                output, error = run_generated_code()
                model_time = parse_output(output)
                error_type = categorize_error(error) if error else None
            except ValueError as e:
                print(f"Error: {e}")
                model_time = None
                error_type = "ValueError"

            # Print the formatted output to the terminal
            timestamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            print(f"{example_id}. [{timestamp}] | PROMPT TYPE: {prompt_type} | ANSWER: {model_time} EXPECTED: {expected_time} | ERROR: {error_type}")

            # Write to the text file
            txt_file.write(f"{example_id}. [{timestamp}] | PROMPT TYPE: {prompt_type} | ANSWER: {model_time} EXPECTED: {expected_time} | ERROR: {error_type}\n")
            
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
                if not error_type:
                    no_error_0shot += 1
            else:
                results_5shot.append(result_entry)
                total_5shot += 1
                if model_time == expected_time:
                    correct_5shot += 1
                if not error_type:
                    no_error_5shot += 1
    
    # Calculate accuracies
    accuracy_0shot = (correct_0shot / total_0shot) * 100 if total_0shot > 0 else 0
    accuracy_5shot = (correct_5shot / total_5shot) * 100 if total_5shot > 0 else 0
    total_accuracy = ((correct_0shot + correct_5shot) / (total_0shot + total_5shot)) * 100 if (total_0shot + total_5shot) > 0 else 0
    
    # Calculate no-error accuracies
    no_error_accuracy_0shot = (correct_0shot / no_error_0shot) * 100 if no_error_0shot > 0 else 0
    no_error_accuracy_5shot = (correct_5shot / no_error_5shot) * 100 if no_error_5shot > 0 else 0
    
    # Write the final accuracy to the text file
    end_time = datetime.datetime.now()
    total_time = end_time - start_time
    txt_file.write(f"\n0-shot prompts: Model guessed {correct_0shot} out of {total_0shot} correctly.\n")
    txt_file.write(f"Accuracy: {accuracy_0shot:.2f}%\n")
    txt_file.write(f"5-shot prompts: Model guessed {correct_5shot} out of {total_5shot} correctly.\n")
    txt_file.write(f"Accuracy: {accuracy_5shot:.2f}%\n")
    txt_file.write(f"Total accuracy: {total_accuracy:.2f}%\n")
    txt_file.write(f"0-shot prompts with no errors: {correct_0shot} out of {no_error_0shot} produced real outputs.\n")
    txt_file.write(f"No-error accuracy: {no_error_accuracy_0shot:.2f}%\n")
    txt_file.write(f"5-shot prompts with no errors: {correct_5shot} out of {no_error_5shot} produced real outputs.\n")
    txt_file.write(f"No-error accuracy: {no_error_accuracy_5shot:.2f}%\n")
    txt_file.write(f"Total time taken: {total_time.total_seconds():.2f} seconds\n")
    
    # Write the JSON output
    json_output = {
        "0shot": results_0shot,
        "5shot": results_5shot
    }
    json.dump(json_output, json_file, indent=4)

print("Processing complete. Results saved to model_results.txt and model_results.json.")


# import argparse
# import asyncio
# import json
# import datetime
# import outlines
# import transformers
# import re
# import subprocess
# from kani import Kani
# from kani.engines.huggingface import HuggingEngine
# from kani.engines import WrapperEngine

# # Define the JSON schema for the code output
# JSON_SCHEMA = {
#     "type": "object",
#     "properties": {
#         "explanation": {
#             "type": "string"
#         },
#         "code": {
#             "type": "string",
#             "pattern": "^\"\"\\n'''python\\n([\\s\\S]+)\\n'''\\n\"\"\"$"
#         }
#     },
#     "required": ["explanation", "code"]
# }

# # Load the calendar scheduling examples from the JSON file
# with open('100_prompt_scheduling.json', 'r') as file:
#     calendar_examples = json.load(file)

# # Argument parser to select the model
# parser = argparse.ArgumentParser(description="Select a HuggingFace model.")
# parser.add_argument('--model', type=str, required=True, help="The HuggingFace model ID to use.")
# args = parser.parse_args()

# # Load the model selected by the user
# class JSONGuidanceHFWrapper(WrapperEngine):
#     def __init__(self, engine: HuggingEngine, *args, json_schema, **kwargs):
#         super().__init__(engine, *args, **kwargs)
#         # keep a reference to the JSON schema we want to use
#         self.engine: HuggingEngine  # type hint for IDEs
#         self.json_schema = json_schema
#         self.outlines_tokenizer = outlines.models.TransformerTokenizer(self.engine.tokenizer)

#     def _create_logits_processor(self):
#         json_logits_processor = outlines.processors.JSONLogitsProcessor(self.json_schema, self.outlines_tokenizer)
#         return transformers.LogitsProcessorList([json_logits_processor])

#     async def predict(self, *args, **kwargs):
#         # each time we call predict or stream, pass a new instance of JSONLogitsProcessor
#         if "logits_processor" not in kwargs:
#             kwargs["logits_processor"] = self._create_logits_processor()
#         return await super().predict(*args, **kwargs)

#     async def stream(self, *args, **kwargs):
#         # each time we call predict or stream, pass a new instance of JSONLogitsProcessor
#         if "logits_processor" not in kwargs:
#             kwargs["logits_processor"] = self._create_logits_processor()
#         async for elem in super().stream(*args, **kwargs):
#             yield elem

# model = HuggingEngine(model_id=args.model)
# engine = JSONGuidanceHFWrapper(model, json_schema=JSON_SCHEMA)

# # Create the Kani instance
# ai = Kani(engine)

# # Function to parse the golden plan time into {HH:MM:HH:MM} format
# def parse_golden_plan_time(golden_plan):
#     match = re.search(r'(\d{1,2}:\d{2}) - (\d{1,2}:\d{2})', golden_plan)
#     if match:
#         start_time, end_time = match.groups()
#         return f"{{{start_time}:{end_time}}}"
#     return "Invalid format"

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

# # Function to extract code from the model response
# def extract_code(model_response):
#     """
#     Extract the code block from the model response.
#     The code is expected to be wrapped in triple quotes and start with '''python.
#     """
#     match = re.search(r"'''python\n([\s\S]+?)\n'''", model_response)
#     if match:
#         code = match.group(1)
#     else:
#         raise ValueError("Could not extract code from the model response.")
#     return code

# # Function to write code to a file
# def write_code_to_file(code, filename="generated_code.py"):
#     with open(filename, "w") as f:
#         f.write(code)

# # Function to execute the generated code
# def execute_code(filename="generated_code.py"):
#     result = subprocess.run(["python3", filename], capture_output=True, text=True)
#     if result.returncode == 0:
#         return result.stdout.strip(), None  # No error
#     else:
#         error_category = categorize_error(result.stderr.strip())
#         return f"Error: {result.stderr.strip()}", error_category

# # Initialize counters for accuracy calculation
# correct_0shot = 0
# correct_5shot = 0
# total_0shot = 0
# total_5shot = 0

# # Initialize lists to store 0-shot and 5-shot results
# results_0shot = []
# results_5shot = []

# # Open the text file for writing results
# with open('ML-ML-3.1-8B_code_txtresults.txt', 'w') as txt_file, open('ML-ML-3.1-8B_code_jsonresults.json', 'w') as json_file:
#     start_time = datetime.datetime.now()
    
#     for example_id, example in calendar_examples.items():
#         for prompt_type in ['prompt_0shot', 'prompt_5shot']:
#             prompt = example[prompt_type]
#             golden_plan = example['golden_plan']

#             # Parse golden plan into {HH:MM:HH:MM} format
#             expected_time = parse_golden_plan_time(golden_plan)

#             # Append the suffix to the prompt
#             prompt += "\n\nPlease generate a full Python script program which calculates the proposed time. Ensure the code is clean, well-formatted, and free from unnecessary escape characters or tags. Generate a response in the following JSON format. Ensure the code is enclosed within double quotes in the beginning (\"\") and triple quotes at the end, and starts with '''python. Use proper indentation and spacing. Finally, make sure the output of the program you generate displays the calculated time in the following format: {HH:MM:HH:MM}. Here is an example of a possible format of time: {14:30:15:30}. The final time must be encased in curly brackets: {}. Do not generate any text or code after you output the correct JSON format."

#             # Run the model and capture the response
#             async def get_model_response():
#                 full_response = ""
#                 async for token in ai.chat_round_stream(prompt):
#                     full_response += token
#                     print(token, end="", flush=True)
#                 print()  # For a newline after the response
#                 return full_response.strip()  # Return the actual response
            
#             model_response = asyncio.run(get_model_response())

#             # Extract the code from the model response
#             try:
#                 code = extract_code(model_response)
#             except ValueError as e:
#                 print(f"Error: {e}")
#                 model_time = "Invalid response"
#                 error_category = "Code extraction failed"
#             else:
#                 # Write the code to a file
#                 write_code_to_file(code)
                
#                 # Execute the generated code and capture the output
#                 execution_output, error_category = execute_code()
#                 if execution_output.startswith("Error:"):
#                     model_time = "Invalid response"
#                 else:
#                     # Extract the time range from the executed code's output
#                     match = re.search(r'\{(\d{1,2}:\d{2}:\d{1,2}:\d{2})\}', execution_output)
#                     if match:
#                         model_time = match.group(0)
#                     else:
#                         model_time = "Invalid response"
#                         error_category = "Time extraction failed"
            
#             # Print the formatted output to the terminal
#             timestamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
#             print(f"{example_id}. [{timestamp}] | PROMPT TYPE: {prompt_type} | ANSWER: {model_time} EXPECTED: {expected_time} | ERROR: {error_category}")

#             # Write to the text file immediately
#             txt_file.write(f"{example_id}. [{timestamp}] | PROMPT TYPE: {prompt_type} | ANSWER: {model_time} EXPECTED: {expected_time} | ERROR: {error_category}\n")
            
#             # Prepare the JSON output
#             result_entry = {
#                 "final_time": f"{model_time}",
#                 "expected_time": f"{expected_time}",
#                 "exact_response": model_response,
#                 "error_category": error_category,
#                 "count": example_id
#             }
            
#             # Append the result to the appropriate list
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
            
#             # Clear the model_response and other temporary variables from memory
#             del model_response, model_time, result_entry, error_category
            
#     # Write the collected results to the JSON file in the desired format
#     json.dump({
#         "0shot": results_0shot,
#         "5shot": results_5shot
#     }, json_file, indent=4)
    
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

# print("Processing complete. Results saved to ML-ML-3.1-8B_code_txtresults.txt and ML-ML-3.1-8B_code_jsonresults.json.")



# import argparse
# import asyncio
# import json
# import datetime
# import outlines
# import transformers
# import re
# import subprocess
# from kani import Kani
# from kani.engines.huggingface import HuggingEngine
# from kani.engines import WrapperEngine

# # Define the JSON schema for the code output
# JSON_SCHEMA = {
#     "type": "object",
#     "properties": {
#         "explanation": {
#             "type": "string"
#         },
#         "code": {
#             "type": "string"
#         }
#     },
#     "required": ["explanation", "code"]
# }

# # Load the calendar scheduling examples from the JSON file
# with open('100_prompt_scheduling.json', 'r') as file:
#     calendar_examples = json.load(file)

# # Argument parser to select the model
# parser = argparse.ArgumentParser(description="Select a HuggingFace model.")
# parser.add_argument('--model', type=str, required=True, help="The HuggingFace model ID to use.")
# args = parser.parse_args()

# # Load the model selected by the user
# class JSONGuidanceHFWrapper(WrapperEngine):
#     def __init__(self, engine: HuggingEngine, *args, json_schema, **kwargs):
#         super().__init__(engine, *args, **kwargs)
#         # keep a reference to the JSON schema we want to use
#         self.engine: HuggingEngine  # type hint for IDEs
#         self.json_schema = json_schema
#         self.outlines_tokenizer = outlines.models.TransformerTokenizer(self.engine.tokenizer)

#     def _create_logits_processor(self):
#         json_logits_processor = outlines.processors.JSONLogitsProcessor(self.json_schema, self.outlines_tokenizer)
#         return transformers.LogitsProcessorList([json_logits_processor])

#     async def predict(self, *args, **kwargs):
#         # each time we call predict or stream, pass a new instance of JSONLogitsProcessor
#         if "logits_processor" not in kwargs:
#             kwargs["logits_processor"] = self._create_logits_processor()
#         return await super().predict(*args, **kwargs)

#     async def stream(self, *args, **kwargs):
#         # each time we call predict or stream, pass a new instance of JSONLogitsProcessor
#         if "logits_processor" not in kwargs:
#             kwargs["logits_processor"] = self._create_logits_processor()
#         async for elem in super().stream(*args, **kwargs):
#             yield elem

# model = HuggingEngine(model_id=args.model)
# engine = JSONGuidanceHFWrapper(model, json_schema=JSON_SCHEMA)

# # Create the Kani instance
# ai = Kani(engine)

# # Function to parse the golden plan time into {HH:MM:HH:MM} format
# def parse_golden_plan_time(golden_plan):
#     match = re.search(r'(\d{1,2}:\d{2}) - (\d{1,2}:\d{2})', golden_plan)
#     if match:
#         start_time, end_time = match.groups()
#         return f"{{{start_time}:{end_time}}}"
#     return "Invalid format"

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

# # Initialize counters for accuracy calculation
# correct_0shot = 0
# correct_5shot = 0
# total_0shot = 0
# total_5shot = 0

# # Initialize lists to store 0-shot and 5-shot results
# results_0shot = []
# results_5shot = []

# # Open the text file for writing results
# with open('ML-ML-3.1-8B_code_txtresults.txt', 'w') as txt_file, open('ML-ML-3.1-8B_code_jsonresults.json', 'w') as json_file:
#     start_time = datetime.datetime.now()
    
#     for example_id, example in calendar_examples.items():
#         for prompt_type in ['prompt_0shot', 'prompt_5shot']:
#             prompt = example[prompt_type]
#             golden_plan = example['golden_plan']

#             # Parse golden plan into {HH:MM:HH:MM} format
#             expected_time = parse_golden_plan_time(golden_plan)

#             # Append the suffix to the prompt
#             prompt += "\n\nPlease generate a Python script that outputs the proposed time." \
                # "Your response must be in the following JSON format:\n" \
                # "{\n" \
                # "  \"explanation\": \"Any text surrounding the code here\",\n" \
                # "  \"code\": \"```python\\n# Your complete Python program here\\n```\"\n" \
                # "}\n"
            
#             # Run the model and capture the response
#             async def get_model_response():
#                 full_response = ""
#                 async for token in ai.chat_round_stream(prompt):
#                     full_response += token
#                     print(token, end="", flush=True)
#                 print()  # For a newline after the response
#                 return full_response.strip()  # Return the actual response
            
#             model_response = asyncio.run(get_model_response())

#             def extract_code(response):
#                 """Extracts the code from the model's response."""
#                 try:
#                     response_dict = json.loads(response)
#                     return response_dict.get("code", "Invalid response")
#                 except json.JSONDecodeError:
#                     return "Invalid response"
            
#             def execute_code(code):
#                 """Executes the generated code and captures the output."""
#                 try:
#                     with open('generated_code.py', 'w') as code_file:
#                         code_file.write(code)
#                     result = subprocess.run(['python3', 'generated_code.py'], capture_output=True, text=True)
#                     if result.returncode == 0:
#                         return result.stdout.strip(), None  # No error
#                     else:
#                         error_category = categorize_error(result.stderr.strip())
#                         return f"Error: {result.stderr.strip()}", error_category
#                 except Exception as e:
#                     error_category = categorize_error(str(e))
#                     return f"Error: {str(e)}", error_category
            
#             def extract_time_range(output):
#                 """Extracts HH:MM:HH:MM format from the executed code's output."""
#                 match = re.search(r'\{(\d{1,2}:\d{2}:\d{1,2}:\d{2})\}', output)
#                 if match:
#                     return match.group(0)
#                 return "Invalid response"
            
#             if model_response:
#                 code = extract_code(model_response)
#                 if code == "Invalid response":
#                     model_time = "Invalid response"
#                     error_category = "Invalid JSON response"
#                 else:
#                     execution_output, error_category = execute_code(code)
#                     if execution_output.startswith("Error:"):
#                         model_time = "Invalid response"
#                     else:
#                         model_time = extract_time_range(execution_output)
#             else:
#                 model_time = "Invalid response"
#                 error_category = "No response from model"
            
#             # Print the formatted output to the terminal
#             timestamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
#             print(f"{example_id}. [{timestamp}] | PROMPT TYPE: {prompt_type} | ANSWER: {model_time} EXPECTED: {expected_time} | ERROR: {error_category}")

#             # Write to the text file immediately
#             txt_file.write(f"{example_id}. [{timestamp}] | PROMPT TYPE: {prompt_type} | ANSWER: {model_time} EXPECTED: {expected_time} | ERROR: {error_category}\n")
            
#             # Prepare the JSON output
#             result_entry = {
#                 "final_time": f"{model_time}",
#                 "expected_time": f"{expected_time}",
#                 "exact_response": model_response,
#                 "error_category": error_category,
#                 "count": example_id
#             }
            
#             # Append the result to the appropriate list
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
            
#             # Clear the model_response and other temporary variables from memory
#             del model_response, model_time, result_entry, error_category
            
#     # Write the collected results to the JSON file in the desired format
#     json.dump({
#         "0shot": results_0shot,
#         "5shot": results_5shot
#     }, json_file, indent=4)
    
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

# print("Processing complete. Results saved to ML-ML-3.1-8B_code_txtresults.txt and ML-ML-3.1-8B_code_jsonresults.json.")



# import asyncio
# import json
# import os
# import sys
# from argparse import ArgumentParser
# import argparse
# from datetime import datetime, timedelta
# import torch
# import subprocess
# from kani import Kani
# from kani.engines.huggingface import HuggingEngine
# from kani.engines import WrapperEngine
# import outlines
# import transformers
# import re

# # Initialize the json schema format
# JSON_SCHEMA = {
#     "type": "object",
#     "properties": {
#         "explanation": {
#             "type": "string"
#         },
#         "code": {
#             "type": "string"
#         }
#     },
#     "required": ["explanation", "code"]
# }

# # Argument parser to select the model
# parser = argparse.ArgumentParser(description="Select a HuggingFace model.")
# parser.add_argument('--model', type=str, required=True, help="The HuggingFace model ID to use.")
# args = parser.parse_args()

# # Load the model selected by the user
# class JSONGuidanceHFWrapper(WrapperEngine):
#     def __init__(self, engine: HuggingEngine, *args, json_schema, **kwargs):
#         super().__init__(engine, *args, **kwargs)
#         # keep a reference to the JSON schema we want to use
#         self.engine: HuggingEngine  # type hint for IDEs
#         self.json_schema = json_schema
#         self.outlines_tokenizer = outlines.models.TransformerTokenizer(self.engine.tokenizer)

#     def _create_logits_processor(self):
#         json_logits_processor = outlines.processors.JSONLogitsProcessor(self.json_schema, self.outlines_tokenizer)
#         return transformers.LogitsProcessorList([json_logits_processor])

#     async def predict(self, *args, **kwargs):
#         # each time we call predict or stream, pass a new instance of JSONLogitsProcessor
#         if "logits_processor" not in kwargs:
#             kwargs["logits_processor"] = self._create_logits_processor()
#         return await super().predict(*args, **kwargs)

#     async def stream(self, *args, **kwargs):
#         # each time we call predict or stream, pass a new instance of JSONLogitsProcessor
#         if "logits_processor" not in kwargs:
#             kwargs["logits_processor"] = self._create_logits_processor()
#         async for elem in super().stream(*args, **kwargs):
#             yield elem

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
#     "\nWrite a **complete and executable Python program** that calculates and outputs the desired meeting time range in the exact format {HH:MM:HH:MM}. "
#     "The program must include all necessary logic, such as defining participant schedules, calculating available time slots, and outputting the result. "
#     "The code should be the primary focus of your response, and the explanation should be concise.\n"
    # "Your response must be in the following JSON format:\n"
    # "{\n"
    # "  \"explanation\": \"Any text surrounding the code here\",\n"
    # "  \"code\": \"```python\\n# Your complete Python program here\\n```\"\n"
    # "}\n"
#     "The code must be fully executable and should not contain placeholders, comments without code, or incomplete snippets. "
#     "Ensure the program outputs exactly one time range in the format {HH:MM:HH:MM}."
# )

# # Initialize the model engine.
# def initialize_engine(model_id):
#     try:
#         model = HuggingEngine(model_id=args.model)
#         engine = JSONGuidanceHFWrapper(model, json_schema=JSON_SCHEMA)
#         return engine
#     except Exception as e:
#         print(f"Error initializing model: {e}")  # Debug print
#         raise

# # Function to extract the code from the model's response
# def extract_code(response):
#     """
#     Extracts the Python code block from the response.
#     The code block is expected to start with ```python and end with ```.
#     """
#     start_marker = "```python"
#     end_marker = "```"
    
#     # Find the start of the code block
#     start = response.find(start_marker)
#     if start == -1:
#         # If ```python is not found, try finding just ```
#         start = response.find("```")
#         if start == -1:
#             return None  # No code block found
#         else:
#             start += len("```")
#     else:
#         start += len(start_marker)
    
#     # Find the end of the code block
#     end = response.find(end_marker, start)
#     if end == -1:
#         return None  # No end marker found
    
#     # Extract the code and strip any leading/trailing whitespace
#     code = response[start:end].strip()
    
#     # Handle escaped characters (e.g., \\n, \\", etc.)
#     code = code.replace('\\n', '\n')  # Unescape newlines
#     code = code.replace('\\"', '"')   # Unescape quotes
#     code = code.replace('\\t', '\t')  # Unescape tabs
    
#     # Remove any remaining unwanted characters
#     code = code.strip('"')  # Remove extra quotes at the beginning and end
    
#     return code

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
# def run_generated_code(response):
#     """
#     Extracts the code from the model's response, writes it to generated_code.py, and runs it.
#     """
#     # Extract the code from the response
#     code = extract_code(response)
#     if not code:
#         return None, "NoCodeGenerated"
    
#     try:
#         # Write the extracted code to generated_code.py
#         with open("generated_code.py", "w") as file:
#             file.write(code)
        
#         # Execute the generated code
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

# # Main function to run the model.
# async def run_model():
#     expected_outputs_0shot = []
#     predicted_outputs_0shot = []
#     expected_outputs_5shot = []
#     predicted_outputs_5shot = []
#     start_time_value = datetime.now()

#     # Initialize text results file if it doesn't exist.
#     if not os.path.exists("ML-ML-3.1-8B_json_results.txt"):
#         print("Initializing text results file...")  # Debug print
#         with open("ML-ML-3.1-8B_json_results.txt", "w") as file:
#             file.write("Model Results:\n")

#     # Initialize JSON results file if it doesn't exist.
#     if not os.path.exists("ML-ML-3.1-8B_jsoncode_results.json"):
#         print("Initializing JSON results file...")  # Debug print
#         with open("ML-ML-3.1-8B_jsoncode_results.json", "w") as json_file:
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

#     for i, (key, data) in enumerate(prompts_list):
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

#                         # Extract the code from the response and run it
#                         code_output, error_type = run_generated_code(response)
#                         if code_output:
#                             predicted_time = code_output
#                         else:
#                             predicted_time = None

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

#                         with open("ML-ML-3.1-8B_json_results.txt", "a") as file:
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
#                         with open("ML-ML-3.1-8B_jsoncode_results.json", "r+") as json_file:
#                             file_data = json.load(json_file)
#                             if prompt_type == "prompt_0shot":
#                                 file_data["0shot"].append(json_output)
#                             elif prompt_type == "prompt_5shot":
#                                 file_data["5shot"].append(json_output)
#                             json_file.seek(0)
#                             json.dump(file_data, json_file, indent=4)
#                             json_file.truncate()

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
#     total_elapsed_time = (end_time_value - start_time_value).total_seconds()

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

#     with open("ML-ML-3.1-8B_json_results.txt", "a") as file:
#         file.write(accuracy_line)

# # Run the model.
# if __name__ == "__main__":
#     asyncio.run(run_model())

