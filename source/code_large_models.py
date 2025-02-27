'''
import re
import os
import json
from kani import Kani
from kani.engines.huggingface import HuggingEngine
import asyncio
from argparse import ArgumentParser
from datetime import datetime
import subprocess

# Argument parser for model selection
parser = ArgumentParser()
parser.add_argument("--model", dest="model", help="Model name to use")
args = parser.parse_args()

# Load the prompts from the JSON file
with open("test_scheduling.json", "r") as file:
    prompts_data = json.load(file)

# Define prefix and suffix messages
prefix_message = "You are an expert at scheduling meetings. Please find a suitable time for the following task using a Python program:\n"
suffix_message = """
Give me a program to check the best availability. The output of the program should have the answer in the format of: {start_time:end_time}. The program should include all necessary logic to determine the meeting time based on the task description.
The output should be exactly like this: {10:00:11:00}. Only provide the Python code, as in I want actual code. I need you to produce actual real Python code in the output for the task. Make sure there is no errors in the code and that it runs properly.
The program that is generated should be able to be run and then should follow the task and generate the right output in the exact format above.
"""

# Initialize the model
engine = HuggingEngine(model_id=args.model, use_auth_token=True, model_load_kwargs={"device_map": "auto", "trust_remote_code": True})
ai = Kani(engine)

# Function to extract the time from the model's response
def extract_time(response):
    if "{" in response and "}" in response:
        start = response.find("{")
        end = response.find("}") + 1
        time_str = response[start:end]
        # Remove 'start_time' and 'end_time' labels and keep only the time values
        time_str = time_str.replace("start_time:", "").replace("end_time:", "").replace(" ", "").replace(",", ":")
        return time_str
    return None

# Function to convert the golden plan to dictionary format and remove days of the week
def convert_golden_plan(golden_plan):
    if "Here is the proposed time:" in golden_plan:
        time_part = golden_plan.split(": ")[-1].strip()
        # Remove the day of the week (e.g., "Monday, 14:30" -> "14:30")
        start_time, end_time = time_part.split(" - ")
        start_time = start_time.split(", ")[-1] if ", " in start_time else start_time
        end_time = end_time.split(", ")[-1] if ", " in end_time else end_time
        return f"{{{start_time}:{end_time}}}"
    return None

# Function to calculate accuracy
def calculate_accuracy(expected, predicted):
    correct = 0
    for exp, pred in zip(expected, predicted):
        if exp == pred:
            correct += 1
    return (correct / len(expected)) * 100

# Function to clean the generated code (remove markdown and surrounding text)
def clean_generated_code(response):
    # Use regex to extract Python code from markdown-style code blocks
    code_match = re.search(r"```python(.*?)```", response, re.DOTALL)
    if code_match:
        return code_match.group(1).strip()  # Extract the code and remove leading/trailing whitespace
    return response.strip()  # If no markdown, assume the entire response is code

# Function to run the generated Python code and capture its output
def run_generated_code():
    try:
        result = subprocess.run(['python', 'generate_code.py'], capture_output=True, text=True, check=True)
        return result.stdout.strip()
    except subprocess.CalledProcessError as e:
        return f"Error: {e}"

# Main function to run the model
async def run_model():
    expected_outputs = []
    predicted_outputs = []
    count = 1

    start_time = datetime.now()

    # Open the file to write the results
    with open("ML-ML-3.1-8B_code_results.txt", "w") as file:
        file.write("Model Results:\n")

    for key, data in prompts_data.items():
        # Extract all available prompts for the task
        prompt_types = [k for k in data.keys() if k.startswith("prompt_")]
    
        for prompt_type in prompt_types:
            prompt = data[prompt_type]
            golden_plan = data["golden_plan"]

            # Add prefix and suffix to the prompt
            full_prompt = prefix_message + prompt + suffix_message

            # Get the model's response
            response = await ai.chat_round_str(full_prompt)

            # Clean the generated code (remove markdown and surrounding text)
            cleaned_code = clean_generated_code(response)

            # Write the cleaned code to generate_code.py
            with open("generate_code.py", "w") as code_file:
                code_file.write(cleaned_code)

            # Run the generated code and capture the output
            code_output = run_generated_code()
            if code_output:
                predicted_time = extract_time(code_output)
            else:
                predicted_time = None

            expected_time = convert_golden_plan(golden_plan)

            # Append to lists for accuracy calculation
            expected_outputs.append(expected_time)
            predicted_outputs.append(predicted_time)

            # Get the current timestamp
            timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

            # Display the task, solution, and results
            line = f"\n{count}. [{timestamp}] | CODE OUTPUT: {predicted_time} EXPECTED: {expected_time}\n"
            print(line)

            # Write the output to a file
            with open("ML-ML-3.1-8B_code_results.txt", "a") as file:
                file.write(line)

            count += 1

    # End the timers
    end_time = datetime.now()
    total_time = end_time - start_time
 
    # Calculate and display accuracy
    accuracy = calculate_accuracy(expected_outputs, predicted_outputs)
    accuracy_line = f"\nModel guessed {sum(1 for exp, pred in zip(expected_outputs, predicted_outputs) if exp == pred)} out of {len(expected_outputs)} prompts correctly.\nAccuracy: {accuracy:.2f}%\n"
    print(accuracy_line)
    print(f"Total time taken: {total_time}")

    # Write the output to a file
    with open("ML-ML-3.1-8B_code_results.txt", "a") as file:
        file.writelines(accuracy_line)
        file.write(f"Total time taken: {total_time}")

# Run the model
asyncio.run(run_model())
'''

'''
import os
import json
from kani import Kani
from kani.engines.huggingface import HuggingEngine
import asyncio
from argparse import ArgumentParser
from datetime import datetime
import subprocess

# Argument parser for model selection
parser = ArgumentParser()
parser.add_argument("--model", dest="model", help="Model name to use")
args = parser.parse_args()

# Load the prompts from the JSON file
with open("test_scheduling.json", "r") as file:
    prompts_data = json.load(file)

# Define prefix and suffix messages
prefix_message = "You are an expert at scheduling meetings. Please find a suitable time for the following task:\n"
suffix_message = "\nPlease write a full Python program with actual code that outputs the solution in the format: {start_time: end_time} to find the proper time. The output should be exactly in the format {HH:MM:HH:MM} and should be the only output of the program."

# Initialize the model
engine = HuggingEngine(model_id=args.model, use_auth_token=True, model_load_kwargs={"device_map": "auto", "trust_remote_code": True})
ai = Kani(engine)

# Function to extract Python code from the model's response
def extract_code(response):
    if "```python" in response:
        start = response.find("```python") + len("```python")
        end = response.find("```", start)
        code = response[start:end].strip()
        return code
    return None

# Function to convert the golden plan to dictionary format and remove days of the week
def convert_golden_plan(golden_plan):
    if "Here is the proposed time:" in golden_plan:
        time_part = golden_plan.split(": ")[-1].strip()
        # Remove the day of the week (e.g., "Monday, 14:30" -> "14:30")
        start_time, end_time = time_part.split(" - ")
        start_time = start_time.split(", ")[-1] if ", " in start_time else start_time
        end_time = end_time.split(", ")[-1] if ", " in end_time else end_time
        return f"{{{start_time}:{end_time}}}"
    return None

# Function to calculate accuracy
def calculate_accuracy(expected, predicted):
    correct = 0
    for exp, pred in zip(expected, predicted):
        if exp == pred:
            correct += 1
    return (correct / len(expected)) * 100

# Main function to run the model
async def run_model():
    expected_outputs = []
    predicted_outputs = []
    count = 1

    start_time = datetime.now()

    # Open the file to write the results
    with open("ml-ml-3.1-8B_results.txt", "w") as file:
        file.write("Model Results:\n")

    for key, data in prompts_data.items():
        # Extract all available prompts for the task
        prompt_types = [k for k in data.keys() if k.startswith("prompt_")]
    
        for prompt_type in prompt_types:
            prompt = data[prompt_type]
            golden_plan = data["golden_plan"]

            # Add prefix and suffix to the prompt
            full_prompt = prefix_message + prompt + suffix_message

            # Get the model's response
            response = await ai.chat_round_str(full_prompt)

            # Extract the Python code from the response
            code = extract_code(response)
            if code:
                # Write the code to generate_code.py
                with open("generate_code.py", "w") as code_file:
                    code_file.write(code)

                # Run the generated code and capture the output
                try:
                    result = subprocess.run(["python", "generate_code.py"], capture_output=True, text=True, check=True)
                    output = result.stdout.strip()
                    # Validate the output format
                    if output.startswith("{") and output.endswith("}") and len(output.split(":")) == 4:
                        predicted_time = output
                    else:
                        predicted_time = None
                except subprocess.CalledProcessError:
                    predicted_time = None
            else:
                predicted_time = None

            expected_time = convert_golden_plan(golden_plan)

            # Append to lists for accuracy calculation
            expected_outputs.append(expected_time)
            predicted_outputs.append(predicted_time)

            # Get the current timestamp
            timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

            # Display the task, solution, and results
            line = f"\n{count}. [{timestamp}] | CODE OUTPUT: {predicted_time} EXPECTED: {expected_time}\n"
            print(line)

            # Write the output to a file
            with open("ml-ml-3.1-8B_results.txt", "a") as file:
                file.write(line)

            count += 1

    # End the timers
    end_time = datetime.now()
    total_time = end_time - start_time
 
    # Calculate and display accuracy
    accuracy = calculate_accuracy(expected_outputs, predicted_outputs)
    accuracy_line = f"\nModel guessed {sum(1 for exp, pred in zip(expected_outputs, predicted_outputs) if exp == pred)} out of {len(expected_outputs)} prompts correctly.\nAccuracy: {accuracy:.2f}%\n"
    print(accuracy_line)
    print(f"Total time taken: {total_time}")

    # Write the output to a file
    with open("ml-ml-3.1-8B_results.txt", "a") as file:
        file.writelines(accuracy_line)
        file.write(f"Total time taken: {total_time}")

# Run the model
asyncio.run(run_model())

'''
'''

import os
import json
from kani import Kani
from kani.engines.huggingface import HuggingEngine
import asyncio
from argparse import ArgumentParser
from datetime import datetime
import torch  # For clearing GPU cache
import subprocess  # For running the generated Python script


# Argument parser for model selection
parser = ArgumentParser()
parser.add_argument("--model", dest="model", help="Model name to use")
args = parser.parse_args()


# Load the prompts from the JSON file
with open("100_prompt_scheduling.json", "r") as file:
    prompts_data = json.load(file)


# Define prefix and suffix messages
prefix_message = "You are an expert at scheduling meetings. Your task is to find a suitable time for a meeting based on the participants' schedules and constraints. Follow these rules:\n"
suffix_message = "\nWrite a Python program that outputs the meeting time range in the exact format {HH:MM:HH:MM}. Do not include any extra words, explanations, or other text. Only return the Python code. Example output: print('{14:30:15:30}')."


# Initialize the model
engine = HuggingEngine(model_id=args.model, use_auth_token=True, model_load_kwargs={"device_map": "auto", "trust_remote_code": True})
ai = Kani(engine)


# Function to extract the code from the model's response
def extract_code(response):
    start = response.find("```python")
    if start == -1:
        start = response.find("```")
    if start != -1:
        start += len("```python") if "```python" in response else len("```")
        end = response.find("```", start)
        if end != -1:
            return response[start:end].strip()
    return None


# Function to convert the golden plan to dictionary format and remove days of the week
def convert_golden_plan(golden_plan):
    if "Here is the proposed time:" in golden_plan:
        time_part = golden_plan.split(": ")[-1].strip()
        start_time, end_time = time_part.split(" - ")
        start_time = start_time.split(", ")[-1] if ", " in start_time else start_time
        end_time = end_time.split(", ")[-1] if ", " in end_time else end_time
        return f"{{{start_time}:{end_time}}}"
    return None


# Function to calculate accuracy
def calculate_accuracy(expected, predicted):
    correct = 0
    for exp, pred in zip(expected, predicted):
        if exp == pred:
            correct += 1
    return (correct / len(expected)) * 100


# Function to restart the model
def restart_model():
    global ai
    del ai
    torch.cuda.empty_cache()  # Clear GPU cache
    ai = Kani(engine)  # Reinitialize the model


# Function to save checkpoint and current count
def save_checkpoint(index, count):
    with open("checkpoint.txt", "w") as file:
        file.write(f"{index},{count}")


# Function to load checkpoint and current count
def load_checkpoint():
    if os.path.exists("checkpoint.txt"):
        with open("checkpoint.txt", "r") as file:
            index, count = file.read().strip().split(",")
            return int(index), int(count)  # Ensure count continues correctly
    return 0, 1  # Start from 0 index and count 1 if no checkpoint exists


# Function to run the generated Python script and capture its output
def run_generated_code():
    try:
        result = subprocess.run(["python", "generate_code.py"], capture_output=True, text=True, check=True)
        output = result.stdout.strip()
        return output
    except subprocess.CalledProcessError as e:
        print(f"Error running generated code: {e}")
        return None


# Main function to run the model
async def run_model():
    expected_outputs = []
    predicted_outputs = []
    start_time = datetime.now()


    # Load checkpoint (index, count)
    start_index, count = load_checkpoint()


    # Only write "Model Results:" if the file is empty
    if os.path.exists("ML-ML-3.1-8B_code_results.txt") and os.path.getsize("ML-ML-3.1-8B_code_results.txt") == 0:
        with open("ML-ML-3.1-8B_code_results.txt", "a") as file:
            file.write("Model Results:\n")


    prompts_list = list(prompts_data.items())


    for i in range(start_index, len(prompts_list)):
        key, data = prompts_list[i]
        prompt_types = [k for k in data.keys() if k.startswith("prompt_")]
    
        for prompt_type in prompt_types:
            prompt = data[prompt_type]
            golden_plan = data["golden_plan"]


            full_prompt = prefix_message + prompt + suffix_message


            max_retries = 3
            for retry in range(max_retries):
                try:
                    response = await ai.chat_round_str(full_prompt)
                    code = extract_code(response)
                    if code:
                        with open("generate_code.py", "w") as file:
                            file.write(code)
                        code_output = run_generated_code()
                        if code_output and code_output.startswith("{") and code_output.endswith("}"):
                            predicted_time = code_output
                        else:
                            predicted_time = None
                    else:
                        predicted_time = None


                    expected_time = convert_golden_plan(golden_plan)


                    expected_outputs.append(expected_time)
                    predicted_outputs.append(predicted_time)


                    timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                    line = f"\n{count}. [{timestamp}] | CODE OUTPUT: {predicted_time} EXPECTED: {expected_time}\n"
                    print(line)


                    with open("ML-ML-3.1-8B_code_results.txt", "a") as file:
                        file.write(line)


                    count += 1  # Increment the count
                    break  # Exit retry loop if successful
                except RuntimeError as e:
                    print(f"Error occurred (retry {retry + 1}/{max_retries}): {e}")
                    if retry == max_retries - 1:
                        print("Max retries reached. Skipping this prompt.")
                        break
                except Exception as e:
                    print(f"Unexpected error occurred: {e}")
                    break  # Exit retry loop on unexpected errors


            if count % 5 == 0:
                torch.cuda.empty_cache()
                restart_model()


        # Save checkpoint and current count after each prompt
        save_checkpoint(i + 1, count)


    end_time = datetime.now()
    total_time = end_time - start_time


    accuracy = calculate_accuracy(expected_outputs, predicted_outputs)
    accuracy_line = f"\nModel guessed {sum(1 for exp, pred in zip(expected_outputs, predicted_outputs) if exp == pred)} out of {len(expected_outputs)} prompts correctly.\nAccuracy: {accuracy:.2f}%\n"
    print(accuracy_line)
    print(f"Total time taken: {total_time}")


    with open("ML-ML-3.1-8B_code_results.txt", "a") as file:
        file.writelines(accuracy_line)
        file.write(f"Total time taken: {total_time}")


# Run the model
asyncio.run(run_model())

'''

import os
import json
from kani import Kani
from kani.engines.huggingface import HuggingEngine
import asyncio
from argparse import ArgumentParser
from datetime import datetime
import torch  # For clearing GPU cache
import subprocess  # For running the generated Python script


# Argument parser for model selection
parser = ArgumentParser()
parser.add_argument("--model", dest="model", help="Model name to use")
args = parser.parse_args()


# Load the prompts from the JSON file
with open("100_prompt_scheduling.json", "r") as file:
    prompts_data = json.load(file)


# Define prefix and suffix messages
prefix_message = "You are an expert at scheduling meetings. Your task is to find a suitable time for a meeting based on the participants' schedules and constraints. Follow these rules:\n"
suffix_message = "\nWrite a full Python program wth actual code that outputs the desired meeting time range in the exact format {HH:MM:HH:MM}. Do not include any extra words, explanations, or other text. Only return the Python code. Example output: {14:30:15:30}. I want the final time to include the curly brackets {} on the outer portion of the time, just as the example provided. Lastly, make sure any - or , are removed and the final answer only had : in it surrounded by the time and the curly brackets, for example: {HH:MM:HH:MM}. Please only provide one singular time answer and not multiple."


# Initialize the model
engine = HuggingEngine(model_id=args.model, use_auth_token=True, model_load_kwargs={"device_map": "auto", "trust_remote_code": True})
ai = Kani(engine)


# Function to extract the code from the model's response
def extract_code(response):
    start = response.find("```python")
    if start == -1:
        start = response.find("```")
    if start != -1:
        start += len("```python") if "```python" in response else len("```")
        end = response.find("```", start)
        if end != -1:
            return response[start:end].strip()
    return None


# Function to convert the golden plan to dictionary format and remove days of the week
def convert_golden_plan(golden_plan):
    if "Here is the proposed time:" in golden_plan:
        time_part = golden_plan.split(": ")[-1].strip()
        start_time, end_time = time_part.split(" - ")
        start_time = start_time.split(", ")[-1] if ", " in start_time else start_time
        end_time = end_time.split(", ")[-1] if ", " in end_time else end_time
        return f"{{{start_time}:{end_time}}}"
    return None


# Function to calculate accuracy
def calculate_accuracy(expected, predicted):
    correct = 0
    for exp, pred in zip(expected, predicted):
        if exp == pred:
            correct += 1
    return (correct / len(expected)) * 100


# Function to restart the model
def restart_model():
    global ai
    del ai
    torch.cuda.empty_cache()  # Clear GPU cache
    ai = Kani(engine)  # Reinitialize the model


# Function to save checkpoint and current count
def save_checkpoint(index, count):
    with open("checkpoint.txt", "w") as file:
        file.write(f"{index},{count}")


# Function to load checkpoint and current count
def load_checkpoint():
    if os.path.exists("checkpoint.txt"):
        with open("checkpoint.txt", "r") as file:
            index, count = file.read().strip().split(",")
            return int(index), int(count)  # Ensure count continues correctly
    return 0, 1  # Start from 0 index and count 1 if no checkpoint exists


# Function to run the generated Python script and capture its output
def run_generated_code():
    try:
        result = subprocess.run(["python", "generate_code.py"], capture_output=True, text=True, check=True)
        output = result.stdout.strip()
        return output, True  # Return output and success status
    except subprocess.CalledProcessError as e:
        print(f"Error running generated code: {e}")
        return None, False  # Return None and failure status


# Main function to run the model
async def run_model():
    expected_outputs = []
    predicted_outputs = []
    start_time = datetime.now()

    # Metrics for finer-grained results
    total_prompts = 0
    working_code_count = 0
    correct_output_count = 0

    # Load checkpoint (index, count)
    start_index, count = load_checkpoint()

    # Only write "Model Results:" if the file is empty
    if os.path.exists("DS-R1-DL-8B_code_results.txt") and os.path.getsize("DS-R1-DL-8B_code_results.txt") == 0:
        with open("DS-R1-DL-8B_code_results.txt", "a") as file:
            file.write("Model Results:\n")

    prompts_list = list(prompts_data.items())

    for i in range(start_index, len(prompts_list)):
        key, data = prompts_list[i]
        prompt_types = [k for k in data.keys() if k.startswith("prompt_")]
    
        for prompt_type in prompt_types:
            prompt = data[prompt_type]
            golden_plan = data["golden_plan"]

            full_prompt = prefix_message + prompt + suffix_message

            max_retries = 3
            for retry in range(max_retries):
                try:
                    response = await ai.chat_round_str(full_prompt)
                    code = extract_code(response)
                    if code:
                        with open("generate_code.py", "w") as file:
                            file.write(code)
                        code_output, code_success = run_generated_code()
                        if code_success:
                            working_code_count += 1
                            if code_output and code_output.startswith("{") and code_output.endswith("}"):
                                predicted_time = code_output
                                expected_time = convert_golden_plan(golden_plan)
                                if predicted_time == expected_time:
                                    correct_output_count += 1
                            else:
                                predicted_time = None
                        else:
                            predicted_time = None
                    else:
                        predicted_time = None

                    expected_time = convert_golden_plan(golden_plan)
                    expected_outputs.append(expected_time)
                    predicted_outputs.append(predicted_time)

                    timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                    line = f"\n{count}. [{timestamp}] | CODE OUTPUT: {predicted_time} EXPECTED: {expected_time}\n"
                    print(line)

                    with open("DS-R1-DL-8B_code_results.txt", "a") as file:
                        file.write(line)

                    count += 1  # Increment the count
                    total_prompts += 1  # Increment total prompts
                    break  # Exit retry loop if successful
                except RuntimeError as e:
                    print(f"Error occurred (retry {retry + 1}/{max_retries}): {e}")
                    if retry == max_retries - 1:
                        print("Max retries reached. Skipping this prompt.")
                        break
                except Exception as e:
                    print(f"Unexpected error occurred: {e}")
                    break  # Exit retry loop on unexpected errors

            if count % 5 == 0:
                torch.cuda.empty_cache()
                restart_model()

        # Save checkpoint and current count after each prompt
        save_checkpoint(i + 1, count)

    end_time = datetime.now()
    total_time = end_time - start_time

    # Calculate metrics
    accuracy = calculate_accuracy(expected_outputs, predicted_outputs)
    code_success_rate = (working_code_count / total_prompts) * 100
    correct_output_rate = (correct_output_count / working_code_count) * 100 if working_code_count > 0 else 0

    # Print and save results
    results = f"""Model Results:
    - Total Prompts: {total_prompts}
    - Working Code Rate: {code_success_rate:.2f}% ({working_code_count}/{total_prompts})
    - Correct Output Rate (for working code): {correct_output_rate:.2f}% ({correct_output_count}/{working_code_count})
    - Overall Accuracy: {accuracy:.2f}% ({sum(1 for exp, pred in zip(expected_outputs, predicted_outputs) if exp == pred)}/{len(expected_outputs)})
    - Total Time Taken: {total_time}"""
    
    print(results)

    with open("DS-R1-DL-8B_code_results.txt", "a") as file:
        file.write(results)


# Run the model
asyncio.run(run_model())



