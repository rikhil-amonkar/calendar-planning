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

# Define the JSON schema for the code output
JSON_SCHEMA = {
    "type": "object",
    "properties": {
        "python_code": {
            "type": "string",
        }
    },
    "required": ["python_code"],
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

# Initialize counters for accuracy calculation
correct_0shot = 0
correct_5shot = 0
total_0shot = 0
total_5shot = 0

# Initialize lists to store 0-shot and 5-shot results
results_0shot = []
results_5shot = []

# Open the text file for writing results
with open('DS-R1-DL-70B_text_txtresults.txt', 'w') as txt_file, open('DS-R1-DL-70B_json_txtresults.json', 'w') as json_file:
    start_time = datetime.datetime.now()
    
    for example_id, example in calendar_examples.items():
        for prompt_type in ['prompt_0shot', 'prompt_5shot']:
            prompt = example[prompt_type]

            # Append the suffix to the prompt
            prompt += "\n\nPlease output only the Python code in the following JSON format:\n{\"python_code\": \"# Your code here\"}\n\nDo not include any additional text or explanations."

            # Run the model and capture the response
            async def get_model_response():
                full_response = ""
                async for token in ai.chat_round_stream(prompt):
                    full_response += token
                    print(token, end="", flush=True)
                print()  # For a newline after the response
                return full_response.strip()  # Return the actual response
            
            model_response = asyncio.run(get_model_response())

            def extract_and_save_code(response):
                """Extracts Python code from the model's JSON response and saves it to generated_code.py."""
                if not response or not isinstance(response, str):  # Check if response is None or not a string
                    return "Invalid response"
                
                try:
                    # Parse the JSON response
                    response_json = json.loads(response)
                    
                    # Extract the Python code
                    python_code = response_json.get("python_code", "")
                    
                    if not python_code:
                        return "No 'python_code' key found in JSON response"
                    
                    # Replace escaped newlines with actual newlines
                    python_code = python_code.replace("\\n", "\n")
                    
                    # Save the code to generated_code.py
                    with open('generated_code.py', 'w') as code_file:
                        code_file.write(python_code)
                    
                    return "Code successfully saved to generated_code.py"
                except json.JSONDecodeError:
                    return "Invalid JSON response"
                except Exception as e:
                    return f"Error processing response: {e}"
            
            def execute_code():
                """Executes the generated code and captures its output or errors."""
                try:
                    result = subprocess.run(
                        ["python", "generated_code.py"],
                        capture_output=True,
                        text=True,
                        check=True
                    )
                    return result.stdout.strip()
                except subprocess.CalledProcessError as e:
                    return f"Error executing code: {e.stderr.strip()}"
                except Exception as e:
                    return f"Unexpected error: {str(e)}"
            
            if model_response:
                save_result = extract_and_save_code(model_response)
                execution_result = execute_code()
            else:
                save_result = "Invalid response"
                execution_result = "No code to execute"
                   
            # Print the formatted output to the terminal
            timestamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            print(f"{example_id}. [{timestamp}] | PROMPT TYPE: {prompt_type} | SAVE RESULT: {save_result} | EXECUTION RESULT: {execution_result}")

            # Write to the text file immediately
            txt_file.write(f"{example_id}. [{timestamp}] | PROMPT TYPE: {prompt_type} | SAVE RESULT: {save_result} | EXECUTION RESULT: {execution_result}\n")
            
            # Prepare the JSON output
            result_entry = {
                "save_result": save_result,
                "execution_result": execution_result,
                "exact_response": model_response,
                "count": example_id
            }
            
            # Append the result to the appropriate list
            if prompt_type == 'prompt_0shot':
                results_0shot.append(result_entry)
                total_0shot += 1
                if save_result == "Code successfully saved to generated_code.py" and "Error" not in execution_result:
                    correct_0shot += 1
            else:
                results_5shot.append(result_entry)
                total_5shot += 1
                if save_result == "Code successfully saved to generated_code.py" and "Error" not in execution_result:
                    correct_5shot += 1
            
            # Clear the model_response and other temporary variables from memory
            del model_response, save_result, execution_result, result_entry
            
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
    txt_file.write(f"\n0-shot prompts: Model successfully saved and executed code {correct_0shot} out of {total_0shot} times.\n")
    txt_file.write(f"Accuracy: {accuracy_0shot:.2f}%\n")
    txt_file.write(f"5-shot prompts: Model successfully saved and executed code {correct_5shot} out of {total_5shot} times.\n")
    txt_file.write(f"Accuracy: {accuracy_5shot:.2f}%\n")
    txt_file.write(f"Total accuracy: {total_accuracy:.2f}%\n")
    txt_file.write(f"Total time taken: {total_time}\n")

print("Processing complete. Results saved to DS-R1-DL-70B_text_txtresults.txt and DS-R1-DL-70B_json_txtresults.json.")





