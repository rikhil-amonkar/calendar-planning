# import os
# from kani import Kani
# from kani.engines.openai import OpenAIEngine
# import asyncio
# from argparse import ArgumentParser
# parser = ArgumentParser()
# parser.add_argument("--model", dest="model", help="Model name to use")

# model_name = parser.parse_args().model
# api_key = open('/home/rma336/openai_research/openai_api_key.txt').read()
# engine = OpenAIEngine(api_key, model=model_name)
# ai = Kani(engine, system_prompt="")

# async def run_model():
#     message = f"Which progressive metal band is the best?"
#     response = await ai.chat_round_str(message)
#     print(response)

# asyncio.run(run_model())

'''


import json
import asyncio
import logging
import os
from argparse import ArgumentParser
from datetime import datetime
from kani import Kani
from kani.engines.openai import OpenAIEngine

# PATH FOR KEY: /home/rma336/openai_research/openai_api_key.txt

# Configure logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')

# Define a JSON schema for the forced JSON output.
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

# Set up the argument parser for model selection and API key
parser = ArgumentParser()
parser.add_argument("--model", dest="model", help="Model name to use (e.g., gpt-o3-mini-2025-01-31)", required=True)
parser.add_argument("--api_key", dest="api_key", help="Path to the API key file", required=True)
args = parser.parse_args()

# Load the prompts from the JSON file
def load_prompts(file_path):
    try:
        print(f"Loading prompts from {file_path}...")  # Debug print
        with open(file_path, "r") as file:
            prompts = json.load(file)
            print(f"Successfully loaded {len(prompts)} prompts.")  # Debug print
            return prompts
    except Exception as e:
        print(f"Error loading prompts: {e}")  # Debug print
        raise

# Define prefix and suffix messages.
prefix_message = (
    "You are an expert at scheduling meetings. Your task is to find a suitable time for a meeting "
    "based on the participants' schedules and constraints. Follow these rules:\n"
)
suffix_message = (
    "\nProvide your answer as a JSON object exactly in the following format:\n"
    '{"time_range": "{HH:MM:HH:MM}"}\n'
    "Do not include any extra words, explanations, or other text."
    'Here is an example of an output: {"time_range": "{14:30:15:30}".'
)

# Initialize the OpenAI engine.
def initialize_engine(api_key, model_id):
    try:
        engine = OpenAIEngine(api_key, model=model_id)
        return engine
    except Exception as e:
        print(f"Error initializing model: {e}")  # Debug print
        raise

# Helper function to normalize time format (only remove leading zeros from the hour part)
def normalize_time_format(time_str):
    if time_str and time_str.startswith("{") and time_str.endswith("}"):
        time_str = time_str[1:-1]  # Remove the curly braces
        parts = time_str.split(":")
        if len(parts) >= 2:  # Ensure there are at least hours and minutes
            # Normalize only the hour part (first part)
            hour_part = parts[0]
            normalized_hour = str(int(hour_part))  # Remove leading zeros
            # Reconstruct the time string with normalized hour
            normalized_time = f"{{{normalized_hour}:{':'.join(parts[1:])}}}"
            return normalized_time
    return time_str  # Return the original string if it doesn't match the expected format

# Function to parse the model’s JSON response.
def extract_time_from_json(response):
    try:
        data = json.loads(response)
        time_range = data.get("time_range")
        if time_range and not time_range.startswith("{"):
            time_range = f"{{{time_range}}}"
        time_range = normalize_time_format(time_range)  # Normalize the time format
        print(f"Extracted time: {time_range}")  # Debug print
        return time_range
    except json.JSONDecodeError:
        start = response.find("{")
        end = response.rfind("}")
        if start != -1 and end != -1:
            try:
                data = json.loads(response[start : end + 1])
                time_range = data.get("time_range")
                if time_range and not time_range.startswith("{"):
                    time_range = f"{{{time_range}}}"
                time_range = normalize_time_format(time_range)  # Normalize the time format
                print(f"Extracted time from substring: {time_range}")  # Debug print
                return time_range
            except Exception:
                print("Failed to extract time from substring.")  # Debug print
                return None
        else:
            print("No valid JSON substring found.")  # Debug print
            return None

# Function to convert the golden plan to dictionary format and remove days of the week.
def convert_golden_plan(golden_plan):
    if "Here is the proposed time:" in golden_plan:
        time_part = golden_plan.split(": ")[-1].strip()
        start_time, end_time = time_part.split(" - ")
        start_time = start_time.split(", ")[-1] if ", " in start_time else start_time
        end_time = end_time.split(", ")[-1] if ", " in end_time else end_time
        time_range = f"{{{start_time}:{end_time}}}"
        return normalize_time_format(time_range)  # Normalize the time format
    return None

# Function to calculate accuracy.
def calculate_accuracy(expected, predicted):
    correct = sum(1 for exp, pred in zip(expected, predicted) if exp == pred)
    accuracy = (correct / len(expected)) * 100 if expected else 0
    print(f"Accuracy calculation: {correct} correct out of {len(expected)}.")  # Debug print
    return accuracy

# Function to restart the model.
def restart_model(engine):
    return Kani(engine)

# Function to save checkpoint and current count.
def save_checkpoint(index, count):
    try:
        with open("checkpoint.txt", "w") as file:
            file.write(f"{index},{count}")
    except Exception as e:
        print(f"Failed to save checkpoint: {e}")  # Debug print

# Function to load checkpoint and current count.
def load_checkpoint():
    if os.path.exists("checkpoint.txt"):
        try:
            with open("checkpoint.txt", "r") as file:
                index, count = file.read().strip().split(",")
                print(f"Loaded checkpoint: index={index}, count={count}")  # Debug print
                return int(index), int(count)
        except Exception as e:
            print(f"Failed to load checkpoint: {e}")  # Debug print
    return 0, 0

# Main function to run the model.
async def run_model():
    expected_outputs_0shot = []
    predicted_outputs_0shot = []
    expected_outputs_5shot = []
    predicted_outputs_5shot = []
    start_time_value = datetime.now()

    # Load checkpoint (index, count)
    start_index, count = load_checkpoint()

    # Initialize text results file if it doesn't exist.
    if not os.path.exists("GPT-3O-M-25-01-31_text_results.txt"):
        print("Initializing text results file...")  # Debug print
        with open("GPT-3O-M-25-01-31_text_results.txt", "w") as file:
            file.write("Model Results:\n")

    # Initialize JSON results file if it doesn't exist.
    if not os.path.exists("GPT-3O-M-25-01-31_json_results.json"):
        print("Initializing JSON results file...")  # Debug print
        with open("GPT-3O-M-25-01-31_json_results.json", "w") as json_file:
            json.dump({"0shot": [], "5shot": []}, json_file)

    prompts_data = load_prompts("100_prompt_scheduling.json")
    prompts_list = list(prompts_data.items())

    # Load API key and initialize the OpenAI engine
    api_key = open(args.api_key).read().strip()
    engine = initialize_engine(api_key, args.model)
    ai = Kani(engine)

    for i in range(start_index, len(prompts_list)):
        key, data = prompts_list[i]

        for prompt_type in ["prompt_0shot", "prompt_5shot"]:
            if prompt_type in data:
                prompt = data[prompt_type]
                golden_plan = data["golden_plan"]
                full_prompt = prefix_message + prompt + suffix_message

                max_retries = 3
                for retry in range(max_retries):
                    try:
                        # Get the full JSON response from the model.
                        response = await ai.chat_round_str(full_prompt)

                        predicted_time = extract_time_from_json(response)
                        expected_time = convert_golden_plan(golden_plan)

                        if predicted_time is None:
                            print(f"No valid time found in JSON response for {prompt_type} in {key}")  # Debug print
                            continue  # Skip if no valid time found

                        # Append results based on prompt type.
                        if prompt_type == "prompt_0shot":
                            expected_outputs_0shot.append(expected_time)
                            predicted_outputs_0shot.append(predicted_time)
                        elif prompt_type == "prompt_5shot":
                            expected_outputs_5shot.append(expected_time)
                            predicted_outputs_5shot.append(predicted_time)

                        timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                        line = (
                            f"\n{key}. [{timestamp}] | PROMPT TYPE: {prompt_type} | ANSWER: {predicted_time} "
                            f"EXPECTED: {expected_time}\n"
                        )
                        print(line)  # Debug print

                        with open("GPT-3O-M-25-01-31_text_results.txt", "a") as file:
                            file.write(line)

                        # Construct JSON output manually.
                        json_output = {
                            "final_time": predicted_time,
                            "expected_time": expected_time,
                            "exact_response": response,
                            "count": key,
                        }

                        # Append JSON output to the appropriate section in the JSON file.
                        with open("GPT-3O-M-25-01-31_json_results.json", "r+") as json_file:
                            file_data = json.load(json_file)
                            if prompt_type == "prompt_0shot":
                                file_data["0shot"].append(json_output)
                            elif prompt_type == "prompt_5shot":
                                file_data["5shot"].append(json_output)
                            json_file.seek(0)
                            json.dump(file_data, json_file, indent=4)
                            json_file.truncate()

                        count += 1  # Increment the count
                        break  # Exit retry loop if successful

                    except RuntimeError as e:
                        print(f"Error occurred (retry {retry + 1}/{max_retries}): {e}")  # Debug print
                        if retry == max_retries - 1:
                            print("Max retries reached. Skipping this prompt.")  # Debug print
                            break
                    except Exception as e:
                        print(f"Unexpected error occurred: {e}")  # Debug print
                        break  # Exit retry loop on unexpected errors

                # Restart the model every 5 prompts.
                if count % 5 == 0:
                    ai = restart_model(engine)

        # Save checkpoint after each prompt.
        save_checkpoint(i + 1, count)

    end_time_value = datetime.now()
    total_time = end_time_value - start_time_value

    # Calculate accuracies.
    accuracy_0shot = calculate_accuracy(expected_outputs_0shot, predicted_outputs_0shot)
    accuracy_5shot = calculate_accuracy(expected_outputs_5shot, predicted_outputs_5shot)
    total_accuracy = calculate_accuracy(
        expected_outputs_0shot + expected_outputs_5shot,
        predicted_outputs_0shot + predicted_outputs_5shot,
    )

    accuracy_line = (
        f"\n0-shot prompts: Model guessed {sum(1 for exp, pred in zip(expected_outputs_0shot, predicted_outputs_0shot) if exp == pred)} out of {len(expected_outputs_0shot)} correctly.\n"
        f"Accuracy: {accuracy_0shot:.2f}%\n"
        f"\n5-shot prompts: Model guessed {sum(1 for exp, pred in zip(expected_outputs_5shot, predicted_outputs_5shot) if exp == pred)} out of {len(expected_outputs_5shot)} correctly.\n"
        f"Accuracy: {accuracy_5shot:.2f}%\n"
        f"\nTotal accuracy: {total_accuracy:.2f}%\n"
        f"\nTotal time taken: {total_time}"
    )

    with open("GPT-3O-M-25-01-31_text_results.txt", "a") as file:
        file.write(accuracy_line)

# Run the model.
if __name__ == "__main__":
    asyncio.run(run_model())

'''

import json
import asyncio
import logging
import os
from argparse import ArgumentParser
from datetime import datetime
from kani import Kani
from kani.engines.openai import OpenAIEngine

# Configure logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')

# Define a JSON schema for the forced JSON output.
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

# Set up the argument parser for model selection and API key
parser = ArgumentParser()
parser.add_argument("--model", dest="model", help="Model name to use (e.g., gpt-o3-mini-2025-01-31)", required=True)
parser.add_argument("--api_key", dest="api_key", help="Path to the API key file", required=True)
args = parser.parse_args()

# Load the prompts from the JSON file
def load_prompts(file_path):
    try:
        print(f"Loading prompts from {file_path}...")  # Debug print
        with open(file_path, "r") as file:
            prompts = json.load(file)
            print(f"Successfully loaded {len(prompts)} prompts.")  # Debug print
            return prompts
    except Exception as e:
        print(f"Error loading prompts: {e}")  # Debug print
        raise

# Define prefix and suffix messages.
prefix_message = (
    "You are an expert at scheduling meetings. Your task is to find a suitable time for a meeting "
    "based on the participants' schedules and constraints. Follow these rules:\n"
)
suffix_message = (
    "\nProvide your answer as a JSON object exactly in the following format:\n"
    '{"time_range": "{HH:MM:HH:MM}"}\n'
    "Do not include any extra words, explanations, or other text."
    'Here is an example of an output: {"time_range": "{14:30:15:30}".'
)

# Initialize the OpenAI engine.
def initialize_engine(api_key, model_id):
    try:
        engine = OpenAIEngine(api_key, model=model_id)
        return engine
    except Exception as e:
        print(f"Error initializing model: {e}")  # Debug print
        raise

# Helper function to normalize time format (only remove leading zeros from the hour part)
def normalize_time_format(time_str):
    if time_str and time_str.startswith("{") and time_str.endswith("}"):
        time_str = time_str[1:-1]  # Remove the curly braces
        parts = time_str.split(":")
        if len(parts) >= 2:  # Ensure there are at least hours and minutes
            # Normalize only the hour part (first part)
            hour_part = parts[0]
            normalized_hour = str(int(hour_part))  # Remove leading zeros
            # Reconstruct the time string with normalized hour
            normalized_time = f"{{{normalized_hour}:{':'.join(parts[1:])}}}"
            return normalized_time
    return time_str  # Return the original string if it doesn't match the expected format

# Function to parse the model’s JSON response.
def extract_time_from_json(response):
    try:
        data = json.loads(response)
        time_range = data.get("time_range")
        if time_range and not time_range.startswith("{"):
            time_range = f"{{{time_range}}}"
        time_range = normalize_time_format(time_range)  # Normalize the time format
        print(f"Extracted time: {time_range}")  # Debug print
        return time_range
    except json.JSONDecodeError:
        start = response.find("{")
        end = response.rfind("}")
        if start != -1 and end != -1:
            try:
                data = json.loads(response[start : end + 1])
                time_range = data.get("time_range")
                if time_range and not time_range.startswith("{"):
                    time_range = f"{{{time_range}}}"
                time_range = normalize_time_format(time_range)  # Normalize the time format
                print(f"Extracted time from substring: {time_range}")  # Debug print
                return time_range
            except Exception:
                print("Failed to extract time from substring.")  # Debug print
                return None
        else:
            print("No valid JSON substring found.")  # Debug print
            return None

# Function to convert the golden plan to dictionary format and remove days of the week.
def convert_golden_plan(golden_plan):
    if "Here is the proposed time:" in golden_plan:
        time_part = golden_plan.split(": ")[-1].strip()
        start_time, end_time = time_part.split(" - ")
        start_time = start_time.split(", ")[-1] if ", " in start_time else start_time
        end_time = end_time.split(", ")[-1] if ", " in end_time else end_time
        time_range = f"{{{start_time}:{end_time}}}"
        return normalize_time_format(time_range)  # Normalize the time format
    return None

# Function to calculate accuracy.
def calculate_accuracy(expected, predicted):
    correct = sum(1 for exp, pred in zip(expected, predicted) if exp == pred)
    accuracy = (correct / len(expected)) * 100 if expected else 0
    print(f"Accuracy calculation: {correct} correct out of {len(expected)}.")  # Debug print
    return accuracy

# Function to restart the model.
def restart_model(engine):
    return Kani(engine)

# Function to save checkpoint and current count.
def save_checkpoint(index, count):
    try:
        with open("checkpoint.txt", "w") as file:
            file.write(f"{index},{count}")
    except Exception as e:
        print(f"Failed to save checkpoint: {e}")  # Debug print

# Function to load checkpoint and current count.
def load_checkpoint():
    if os.path.exists("checkpoint.txt"):
        try:
            with open("checkpoint.txt", "r") as file:
                index, count = file.read().strip().split(",")
                print(f"Loaded checkpoint: index={index}, count={count}")  # Debug print
                return int(index), int(count)
        except Exception as e:
            print(f"Failed to load checkpoint: {e}")  # Debug print
    return 0, 0

# Main function to run the model.
async def run_model():
    expected_outputs_0shot = []
    predicted_outputs_0shot = []
    expected_outputs_5shot = []
    predicted_outputs_5shot = []
    start_time_value = datetime.now()

    # Load checkpoint (index, count)
    start_index, count = load_checkpoint()

    # Initialize text results file if it doesn't exist.
    if not os.path.exists("GPT-3O-M-25-01-31_text_results.txt"):
        print("Initializing text results file...")  # Debug print
        with open("GPT-3O-M-25-01-31_text_results.txt", "w") as file:
            file.write("Model Results:\n")

    # Initialize JSON results file if it doesn't exist.
    if not os.path.exists("GPT-3O-M-25-01-31_json_results.json"):
        print("Initializing JSON results file...")  # Debug print
        with open("GPT-3O-M-25-01-31_json_results.json", "w") as json_file:
            json.dump({"0shot": [], "5shot": []}, json_file)

    prompts_data = load_prompts("100_prompt_scheduling.json")
    prompts_list = list(prompts_data.items())

    # Load API key and initialize the OpenAI engine
    api_key = open(args.api_key).read().strip()
    engine = initialize_engine(api_key, args.model)
    ai = Kani(engine)

    for i in range(start_index, len(prompts_list)):
        key, data = prompts_list[i]

        for prompt_type in ["prompt_0shot", "prompt_5shot"]:
            if prompt_type in data:
                prompt = data[prompt_type]
                golden_plan = data["golden_plan"]
                full_prompt = prefix_message + prompt + suffix_message

                max_retries = 3
                for retry in range(max_retries):
                    try:
                        # Get the full JSON response from the model.
                        response = await ai.chat_round_str(full_prompt)

                        predicted_time = extract_time_from_json(response)
                        expected_time = convert_golden_plan(golden_plan)

                        if predicted_time is None:
                            print(f"No valid time found in JSON response for {prompt_type} in {key}")  # Debug print
                            continue  # Skip if no valid time found

                        # Append results based on prompt type.
                        if prompt_type == "prompt_0shot":
                            expected_outputs_0shot.append(expected_time)
                            predicted_outputs_0shot.append(predicted_time)
                        elif prompt_type == "prompt_5shot":
                            expected_outputs_5shot.append(expected_time)
                            predicted_outputs_5shot.append(predicted_time)

                        timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                        line = (
                            f"\n{key}. [{timestamp}] | PROMPT TYPE: {prompt_type} | ANSWER: {predicted_time} "
                            f"EXPECTED: {expected_time}\n"
                        )
                        print(line)  # Debug print

                        with open("GPT-3O-M-25-01-31_text_results.txt", "a") as file:
                            file.write(line)

                        # Construct JSON output manually.
                        json_output = {
                            "final_time": predicted_time,
                            "expected_time": expected_time,
                            "exact_response": response,
                            "count": key,
                        }

                        # Append JSON output to the appropriate section in the JSON file.
                        with open("GPT-3O-M-25-01-31_json_results.json", "r+") as json_file:
                            file_data = json.load(json_file)
                            if prompt_type == "prompt_0shot":
                                file_data["0shot"].append(json_output)
                            elif prompt_type == "prompt_5shot":
                                file_data["5shot"].append(json_output)
                            json_file.seek(0)
                            json.dump(file_data, json_file, indent=4)
                            json_file.truncate()

                        count += 1  # Increment the count
                        break  # Exit retry loop if successful

                    except RuntimeError as e:
                        print(f"Error occurred (retry {retry + 1}/{max_retries}): {e}")  # Debug print
                        if retry == max_retries - 1:
                            print("Max retries reached. Skipping this prompt.")  # Debug print
                            break
                    except Exception as e:
                        print(f"Unexpected error occurred: {e}")  # Debug print
                        break  # Exit retry loop on unexpected errors

                # Restart the model every 5 prompts.
                if count % 5 == 0:
                    ai = restart_model(engine)

        # Save checkpoint after each prompt.
        save_checkpoint(i + 1, count)

    end_time_value = datetime.now()
    total_time = end_time_value - start_time_value

    # Calculate accuracies.
    accuracy_0shot = calculate_accuracy(expected_outputs_0shot, predicted_outputs_0shot)
    accuracy_5shot = calculate_accuracy(expected_outputs_5shot, predicted_outputs_5shot)
    total_accuracy = calculate_accuracy(
        expected_outputs_0shot + expected_outputs_5shot,
        predicted_outputs_0shot + predicted_outputs_5shot,
    )

    accuracy_line = (
        f"\n0-shot prompts: Model guessed {sum(1 for exp, pred in zip(expected_outputs_0shot, predicted_outputs_0shot) if exp == pred)} out of {len(expected_outputs_0shot)} correctly.\n"
        f"Accuracy: {accuracy_0shot:.2f}%\n"
        f"\n5-shot prompts: Model guessed {sum(1 for exp, pred in zip(expected_outputs_5shot, predicted_outputs_5shot) if exp == pred)} out of {len(expected_outputs_5shot)} correctly.\n"
        f"Accuracy: {accuracy_5shot:.2f}%\n"
        f"\nTotal accuracy: {total_accuracy:.2f}%\n"
        f"\nTotal time taken: {total_time}"
    )

    with open("GPT-3O-M-25-01-31_text_results.txt", "a") as file:
        file.write(accuracy_line)

# Run the model.
if __name__ == "__main__":
    asyncio.run(run_model())
