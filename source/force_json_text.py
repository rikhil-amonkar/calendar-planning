# #*****************WORKING JSON FORCE CODE (TEXT OUTPUTS)*************************************

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
with open('100_prompt_scheduling.json', 'r') as file:
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




