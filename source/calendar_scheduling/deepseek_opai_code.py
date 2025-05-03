import asyncio
import argparse
import json
import logging
import os
import re
import subprocess
from argparse import ArgumentParser
from datetime import datetime
from openai import OpenAI

# Read the API key from a file
with open('/home/rma336/openai_research/deepseek_api_key.txt', 'r') as key_file:
    api_key = key_file.read().strip()

client = OpenAI(api_key=api_key, base_url="https://api.deepseek.com")

# Configure logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')

# Set up the argument parser for model selection
# Argument parser to select the model
parser = argparse.ArgumentParser(description="Select an model.")
parser.add_argument('--model', type=str, required=True, help="The model ID to use (e.g., 'deepseek-chat').")
args = parser.parse_args()

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
    "\nGenerate a fully working Python script with code that calculates a proposed time and outputs it in the format HH:MM:HH:MM. " \
    "The script should be clean, well-formatted, and enclosed within '''python and '''. " \
    "The output of the generated code must be a valid time, like {14:30:15:30}. " \
    "Provide the response with only code."
)

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
    # Search for the time pattern without brackets
    time_pattern = re.compile(r"\b\d{2}:\d{2}:\d{2}:\d{2}\b")
    match = time_pattern.search(time_str)
    if match:
        time_str = match.group(0)
        time_str = remove_leading_zeros(time_str)  # Remove leading zeros
        return time_str  # Return the normalized time string
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
        with open("generated_code_2.py", "w") as file:
            file.write(code)
        result = subprocess.run(["python", "generated_code_2.py"], capture_output=True, text=True, check=True)
        output = result.stdout.strip()
        output = normalize_time_format(output)
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

# Function to initialize the JSON results file
def initialize_results_file(file_path):
    if not os.path.exists(file_path):
        with open(file_path, "w") as json_file:
            json.dump({"0shot": []}, json_file, indent=4)

# Main function to run the model
async def run_model():
    expected_outputs_0shot = []
    predicted_outputs_0shot = []
    # expected_outputs_5shot = []
    # predicted_outputs_5shot = []
    start_time = datetime.now()

    prompts_data = load_prompts("calendar_all_1000_prompts.json")
    prompts_list = list(prompts_data.items())

    no_error_count_0shot = 0
    correct_output_count_0shot = 0
    # no_error_count_5shot = 0
    # correct_output_count_5shot = 0

    # Initialize the JSON results file with original naming
    json_results_file = "DS-R1-FULL_json_coderesults.json"
    initialize_results_file(json_results_file)

    for key, data in prompts_list:
        for prompt_type in ["prompt_0shot"]:
            if prompt_type in data:
                prompt = data[prompt_type]
                golden_plan = data["golden_plan"]
                full_prompt = prefix_message + prompt + suffix_message

                try:
                    response = client.chat.completions.create(
                        model=args.model,
                        messages=[
                            {"role": "system", "content": "You are an expert at scheduling meetings."},
                            {"role": "user", "content": full_prompt}
                        ],
                        stream=False
                    )
                    response_content = response.choices[0].message.content
                    # Stop the response after the second '''
                    response_content = stop_after_second_triple_quote(response_content)
                    code = extract_code(response_content)
                    if code:
                        code_output, error_type = run_generated_code(code)
                        predicted_time = code_output if code_output else None
                    else:
                        predicted_time = None
                        error_type = "NoCodeGenerated"

                    expected_time = convert_golden_plan(golden_plan)

                    if prompt_type == "prompt_0shot":
                        expected_outputs_0shot.append(expected_time)
                        predicted_outputs_0shot.append(predicted_time)
                        if error_type is None:
                            no_error_count_0shot += 1
                            if predicted_time == expected_time:
                                correct_output_count_0shot += 1
                    # elif prompt_type == "prompt_5shot":
                    #     expected_outputs_5shot.append(expected_time)
                    #     predicted_outputs_5shot.append(predicted_time)
                    #     if error_type is None:
                    #         no_error_count_5shot += 1
                    #         if predicted_time == expected_time:
                    #             correct_output_count_5shot += 1

                    timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                    line = (
                        f"{key}. [{timestamp}] | PROMPT TYPE: {prompt_type} | ANSWER: {predicted_time} "
                        f"EXPECTED: {expected_time} | ERROR: {error_type}"
                    )
                    logging.info(line)

                    # Use original filename for text results
                    text_results_file = "DS-R1-FULL_text_coderesults.txt"
                    with open(text_results_file, "a") as file:
                        file.write(line + "\n")

                    json_output = {
                        "final_program_time": predicted_time,
                        "expected_time": expected_time,
                        "type_error": error_type,
                        "full_response": response_content,
                        "count": key
                    }

                    with open(json_results_file, "r+") as json_file:
                        file_data = json.load(json_file)
                        if prompt_type == "prompt_0shot":
                            file_data["0shot"].append(json_output)
                        # elif prompt_type == "prompt_5shot":
                        #     file_data["5shot"].append(json_output)
                        json_file.seek(0)
                        json.dump(file_data, json_file, indent=4)
                        json_file.truncate()

                except Exception as e:
                    logging.error(f"Error processing prompt {key}: {e}")

    end_time = datetime.now()
    total_time = (end_time - start_time).total_seconds()

    accuracy_0shot = (correct_output_count_0shot / len(expected_outputs_0shot)) * 100 if expected_outputs_0shot else 0
    # accuracy_5shot = (correct_output_count_5shot / len(expected_outputs_5shot)) * 100 if expected_outputs_5shot else 0
    # total_accuracy = ((correct_output_count_0shot + correct_output_count_5shot) / (len(expected_outputs_0shot) + len(expected_outputs_5shot))) * 100 if (expected_outputs_0shot + expected_outputs_5shot) else 0

    no_error_accuracy_0shot = (correct_output_count_0shot / no_error_count_0shot) * 100 if no_error_count_0shot > 0 else 0
    # no_error_accuracy_5shot = (correct_output_count_5shot / no_error_count_5shot) * 100 if no_error_count_5shot > 0 else 0

    accuracy_line = (
        f"\n0-shot prompts: Model guessed {correct_output_count_0shot} out of {len(expected_outputs_0shot)} correctly.\n"
        f"Accuracy: {accuracy_0shot:.2f}%\n"
        # f"\n5-shot prompts: Model guessed {correct_output_count_5shot} out of {len(expected_outputs_5shot)} correctly.\n"
        # f"Accuracy: {accuracy_5shot:.2f}%\n"
        # f"\nTotal accuracy: {total_accuracy:.2f}%\n"
        f"\n0-shot prompts with no errors: {correct_output_count_0shot} out of {no_error_count_0shot} produced correct outputs.\n"
        f"No-error accuracy: {no_error_accuracy_0shot:.2f}%\n"
        # f"\n5-shot prompts with no errors: {correct_output_count_5shot} out of {no_error_count_5shot} produced correct outputs.\n"
        # f"No-error accuracy: {no_error_accuracy_5shot:.2f}%\n"
        f"\nTotal time taken: {total_time} seconds"
    )

    # Use original filename for text results
    text_results_file = "DS-R1-FULL_text_coderesults.txt"
    with open(text_results_file, "a") as file:
        file.write(accuracy_line)

# Run the model
if __name__ == "__main__":
    asyncio.run(run_model())