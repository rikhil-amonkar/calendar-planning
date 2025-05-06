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
import os

# Define the structured JSON schema for the time range output
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
with open('calendar_all_1000_prompts.json', 'r') as file:
    calendar_examples = json.load(file)

# Argument parser to select the model
parser = argparse.ArgumentParser(description="Select a HuggingFace model.")
parser.add_argument('--model', type=str, required=True, help="The HuggingFace model ID to use.")
args = parser.parse_args()

# State management class
class EvaluationState:
    def __init__(self):
        self.correct_0shot = 0
        self.total_0shot = 0
        self.results_0shot = []
        self.processed_examples = set()
        self.start_time = datetime.datetime.now()
        self.paused_time = datetime.timedelta(0)  # To capture the pause duration
        self.first_run = True
        self.last_paused_time = None  # To capture when the program is paused

    def save(self):
        state_to_save = {
            "correct_0shot": self.correct_0shot,
            "total_0shot": self.total_0shot,
            "results_0shot": self.results_0shot,
            "processed_examples": list(self.processed_examples),
            "start_time": self.start_time.isoformat(),
            "paused_time": self.paused_time.total_seconds(),
            "first_run": self.first_run,
            "last_paused_time": self.last_paused_time.isoformat() if self.last_paused_time else None
        }
        with open(STATE_FILE, 'w') as f:
            json.dump(state_to_save, f)

    def load(self):
        try:
            with open(STATE_FILE, 'r') as f:
                loaded = json.load(f)
                self.correct_0shot = loaded["correct_0shot"]
                self.total_0shot = loaded["total_0shot"]
                self.results_0shot = loaded["results_0shot"]
                self.processed_examples = set(loaded["processed_examples"])
                self.paused_time = datetime.timedelta(seconds=loaded["paused_time"])
                self.start_time = datetime.datetime.fromisoformat(loaded["start_time"])
                self.last_paused_time = datetime.datetime.fromisoformat(loaded["last_paused_time"]) if loaded["last_paused_time"] else None
                self.first_run = loaded.get("first_run", False)
            return True
        except (FileNotFoundError, json.JSONDecodeError, KeyError):
            return False

    def calculate_total_elapsed_time(self):
        if self.last_paused_time:
            total_time = (datetime.datetime.now() - self.start_time) - self.paused_time
        else:
            total_time = (datetime.datetime.now() - self.start_time)
        return total_time

# Define state file location
STATE_FILE = "evaluation_state.json"

class JSONGuidanceHFWrapper(WrapperEngine):
    def __init__(self, engine: HuggingEngine, *args, json_schema, **kwargs):
        super().__init__(engine, *args, **kwargs)
        self.engine: HuggingEngine  # type hint for IDEs
        self.json_schema = json_schema
        self.outlines_tokenizer = outlines.models.TransformerTokenizer(self.engine.tokenizer)

    def _create_logits_processor(self):
        json_logits_processor = outlines.processors.JSONLogitsProcessor(self.json_schema, self.outlines_tokenizer)
        return transformers.LogitsProcessorList([json_logits_processor])

    async def predict(self, *args, **kwargs):
        if "logits_processor" not in kwargs:
            kwargs["logits_processor"] = self._create_logits_processor()
        return await super().predict(*args, **kwargs)

    async def stream(self, *args, **kwargs):
        if "logits_processor" not in kwargs:
            kwargs["logits_processor"] = self._create_logits_processor()
        async for elem in super().stream(*args, **kwargs):
            yield elem

# Create the Kani instance
ai = Kani(JSONGuidanceHFWrapper(HuggingEngine(model_id=args.model), json_schema=JSON_SCHEMA))

# Function to parse the golden plan time into {HH:MM:HH:MM} format
def parse_golden_plan_time(golden_plan):
    match = re.search(r'(\d{1,2}:\d{2}) - (\d{1,2}:\d{2})', golden_plan)
    if match:
        start_time, end_time = match.groups()
        return f"{{{start_time}:{end_time}}}"
    return "Invalid format"

# Initialize state management
state = EvaluationState()
state_loaded = state.load()

# Open the text file for appending results
with open('QWEN-Q-32B_text_txtresults.txt', 'a') as txt_file, open('QWEN-Q-32B_json_txtresults.json', 'a') as json_file:
    start_time = datetime.datetime.now()

    for example_id, example in calendar_examples.items():
        # Skip already processed examples
        if example_id in state.processed_examples:
            continue
        
        for prompt_type in ['prompt_0shot']:
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

            # Check if the model's answer matches the expected time
            if model_time == expected_time:
                state.correct_0shot += 1  # Increment correct count

            state.total_0shot += 1  # Always increment the total count  
                   
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
            state.results_0shot.append(result_entry)
            
            # Clear the model_response and other temporary variables from memory
            del model_response, model_time, result_entry
            
            # Save the current state
            state.processed_examples.add(example_id)
            state.save()
            
    # Write the collected results to the JSON file in the desired format
    json.dump({
        "0shot": state.results_0shot
    }, json_file, indent=4)
    
    # Calculate accuracies
    accuracy_0shot = (state.correct_0shot / state.total_0shot) * 100 if state.total_0shot > 0 else 0
    total_accuracy = ((state.correct_0shot) / (state.total_0shot)) * 100 if (state.total_0shot) > 0 else 0
    
    # Write the final accuracy to the text file
    end_time = datetime.datetime.now()
    total_time = state.calculate_total_elapsed_time()
    txt_file.write(f"\n0-shot prompts: Model guessed {state.correct_0shot} out of {state.total_0shot} correctly.\n")
    txt_file.write(f"Accuracy: {accuracy_0shot:.2f}%\n")
    txt_file.write(f"Total time taken (excluding pauses): {total_time}\n")

print("Processing complete. Results saved to model_results.txt and model_results.json.")
