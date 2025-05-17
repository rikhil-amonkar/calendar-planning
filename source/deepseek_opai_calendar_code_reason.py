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
import tiktoken

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
    "\nGenerate a fully working Python script with code that calculates a proposed time and outputs it in the format HH:MM:HH:MM. "
    "The script should also output the day of the week (e.g., Monday, Tuesday). "
    "The script should be clean, well-formatted, and enclosed within '''python and '''. "
    "The output of the generated code must include both the time range (like {14:30:15:30}) and the day of the week. "
    "Provide the response with only code."
)

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
        with open("generated_code_deepseek.py", "w") as file:
            file.write(code)
        result = subprocess.run(["python", "generated_code_deepseek.py"], 
                              capture_output=True, text=True, check=True)
        output = result.stdout.strip()
        
        # Extract day and time from the output
        day_match = re.search(r'(Monday|Tuesday|Wednesday|Thursday|Friday|Saturday|Sunday)', 
                             output, re.IGNORECASE)
        day = day_match.group(0) if day_match else None
        
        time_output = normalize_time_format(output)
        
        return time_output, day, False  # No error
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

def count_tokens(response_reason):

    """Try to count tokens with fallback to character count if tiktoken fails."""
    try:
            # Define the model (e.g., "gpt-3.5-turbo" or "gpt-4")
            model_name = "gpt-4o" # this doesn't matter
            # Initialize the encoder for the specific model
            encoding = tiktoken.encoding_for_model(model_name)
            # Document to be tokenized
            document = f"{response_reason}"
            # Count the tokens
            tokens = encoding.encode(document)
            token_count = len(tokens)
            return token_count
    except Exception as e:
        print(f"Token counting failed, using fallback method: {str(e)}")

# Function to run the model
async def run_model():
    expected_outputs_0shot = []
    predicted_outputs_0shot = []
    start_time = datetime.now()

    prompts_data = load_prompts("../../data/calendar_scheduling_100.json")
    prompts_list = list(prompts_data.items())

    no_error_count_0shot = 0
    correct_output_count_0shot = 0

    json_results_file = "DS-R1-REASON_code_calendar_results.json"
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
                    response_reason = response.choices[0].message.reasoning_content
                    response_content = stop_after_second_triple_quote(response_content)
                    token_count = count_tokens(response_reason)

                    code = extract_code(response_content)
                    
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
                        expected_outputs_0shot.append((expected_day, expected_time))
                        predicted_outputs_0shot.append((predicted_day, predicted_time))
                        if not has_error:
                            no_error_count_0shot += 1
                            if predicted_time == expected_time and predicted_day == expected_day:
                                correct_output_count_0shot += 1

                    timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                    line = (
                        f"{key}. [{timestamp}] | PROMPT TYPE: {prompt_type} | "
                        f"ANSWER: {predicted_time}, {predicted_day} | "
                        f"EXPECTED: {expected_time}, {expected_day} | "
                        f"REASON COUNT: {token_count} | "
                        f"ERROR: {'Yes' if has_error else 'No'} | "
                        f"REASON COUNT: {token_count}"
                    )
                    logging.info(line)

                    with open("DS-R1-REASON_code_calendar_results.txt", "a") as file:
                        file.write(line + "\n")

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
                        "reasoning_token_count": token_count,
                        "raw_model_response": response_content,
                        "raw_model_reasoning": response_reason,
                        "count": key
                    }

                    with open(json_results_file, "r+") as json_file:
                        file_data = json.load(json_file)
                        file_data["0shot"].append(json_output)
                        json_file.seek(0)
                        json.dump(file_data, json_file, indent=4)
                        json_file.truncate()

                except Exception as e:
                    logging.error(f"Error processing prompt {key}: {e}")

    end_time = datetime.now()
    total_time = (end_time - start_time).total_seconds()

    accuracy_0shot = (correct_output_count_0shot / len(expected_outputs_0shot)) * 100 if expected_outputs_0shot else 0
    no_error_accuracy_0shot = (correct_output_count_0shot / no_error_count_0shot) * 100 if no_error_count_0shot > 0 else 0

    average_token_count = sum(count_tokens(response.choices[0].message.reasoning_content) for response in expected_outputs_0shot) / len(expected_outputs_0shot)

    accuracy_line = (
        f"\n0-shot prompts: Model guessed {correct_output_count_0shot} out of {len(expected_outputs_0shot)} correctly.\n"
        f"Accuracy: {accuracy_0shot:.2f}%\n"
        f"\n0-shot prompts with no errors: {correct_output_count_0shot} out of {no_error_count_0shot} produced correct outputs.\n"
        f"No-error accuracy: {no_error_accuracy_0shot:.2f}%\n"
        f"\nAverage token count for reasoning: {average_token_count:.2f}\n"
        f"\nTotal time taken: {total_time} seconds"
    )

    with open("DS-R1-REASON_code_calendar_results.txt", "a") as file:
        file.write(accuracy_line)

# Run the model
if __name__ == "__main__":
    asyncio.run(run_model())


