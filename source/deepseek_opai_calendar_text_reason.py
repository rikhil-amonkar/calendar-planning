import argparse
import json
import datetime
import re
from openai import OpenAI
import tiktoken

# Read the API key from a file
with open('/home/rma336/openai_research/deepseek_api_key.txt', 'r') as key_file:
    api_key = key_file.read().strip()  # Use .strip() to remove any extra whitespace or newlines

# Initialize the OpenAI client for Deepseek
client = OpenAI(api_key=api_key, base_url="https://api.deepseek.com")

# Load the calendar scheduling examples from the JSON file
with open('../../data/calendar_scheduling_100.json', 'r') as file:
    calendar_examples = json.load(file)

# Argument parser to select the model
parser = argparse.ArgumentParser(description="Select an model.")
parser.add_argument('--model', type=str, required=True, help="The model ID to use (e.g., 'deepseek-chat').")
args = parser.parse_args()

# Function to parse the golden plan time into {HH:MM:HH:MM} format and extract the day of the week
def parse_golden_plan_time(golden_plan):
    match = re.search(r'(\w+), (\d{1,2}:\d{2}) - (\d{1,2}:\d{2})', golden_plan)
    if match:
        day_of_week, start_time, end_time = match.groups()
        return day_of_week, f"{{{start_time}:{end_time}}}"
    return "Invalid day format", "Invalid time format"

# Initialize counters for accuracy calculation
correct_0shot = 0
total_0shot = 0

# Initialize lists to store 0-shot results
results_0shot = []

# Open the text file for writing results
with open('DS-R1-REASON_forceJSON_text_calendar_results.txt', 'w') as txt_file, open('DS-R1-REASON_forceJSON_text_calendar_results.json', 'w') as json_file:
    start_time = datetime.datetime.now()

    for example_id, example in calendar_examples.items():
        for prompt_type in ['prompt_0shot']:
            prompt = example[prompt_type]
            golden_plan = example['golden_plan']

            # Parse golden plan into day and time format
            expected_day, expected_time = parse_golden_plan_time(golden_plan)

            # Append the suffix to the prompt
            prompt += "\n\nPlease output the proposed time in the following JSON format after your reasoning:\n{\"time_range\": \"{HH:MM:HH:MM}\", \"day\": \"<DAY>\"}. For example, if the proposed time is Tuesday, 14:30 to 15:30, the output should be:\n{\"time_range\": \"{14:30:15:30}\", \"day\": \"Tuesday\"}." 
            
            # "For example, if the proposed time is Monday, 14:30 to 15:30, the output should be:\n{\"time_range\": \"{14:30:15:30}\", \"day\": \"Monday\"} If the proposed time is Friday, 09:30 to 10:00, the output should be:\n{\"time_range\": \"{09:30:10:00}\", \"day\": \"Friday\"}.\n\nPlease provide the output in the specified format without any additional text or explanation. The day of the week and time should correspond to the proposed time and day requested.\n\n"

            # Run the model and capture the response
            response = client.chat.completions.create(
                model=args.model,
                messages=[
                    {"role": "system", "content": "You are a helpful assistant."},
                    {"role": "user", "content": prompt}
                ],
                stream=False
            )

            model_reason = response.choices[0].message.reasoning_content
            model_response = response.choices[0].message.content

            # Define the model (e.g., "gpt-3.5-turbo" or "gpt-4")
            model_name = "gpt-4o" # this doesn't matter

            # Initialize the encoder for the specific model
            encoding = tiktoken.encoding_for_model(model_name)

            # Document to be tokenized
            document = f"{model_reason}"

            # Count the tokens
            tokens = encoding.encode(document)
            token_count = len(tokens)
            print(f"Number of Tokens for {example_id}: {token_count}")

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

            # Check if the model has any curly braces in the response
            if "{" in expected_time or "}" in expected_time:
                expected_time = expected_time.replace("{", "").replace("}", "")
            if "{" in model_time or "}" in model_time:
                model_time = model_time.replace("{", "").replace("}", "")

            # Use regex to extract the day of the week
            day_match = re.search(r'"day":"(.*?)"', model_response)
            if not day_match:
                day_match = re.search(r'"day": "(.*?)"', model_response)

            if day_match:
                day_of_week = day_match.group(1).strip()
                print(f"Extracted day of week: {day_of_week}")
            else:
                day_of_week = "Invalid Day"

            # Prepare the JSON output in the new structure
            result_entry = {
                "final_program_time": {
                    "day": day_of_week,
                    "start_time": model_time.split(":")[0] + ":" + model_time.split(":")[1],  # Correcting to show full time
                    "end_time": model_time.split(":")[2] + ":" + model_time.split(":")[3]  # Correcting to show full time
                },
                "expected_time": {
                    "day": expected_day,
                    "start_time": expected_time.split(":")[0] + ":" + expected_time.split(":")[1],  # Correcting to show full time
                    "end_time": expected_time.split(":")[2] + ":" + expected_time.split(":")[3]  # Correcting to show full time
                },
                "reasoning_token_count": token_count,
                "raw_model_response": model_response,
                "raw_model_reasoning": model_reason,
                "count": example_id
            }
            
            # Append the result to the appropriate list
            results_0shot.append(result_entry)
            total_0shot += 1
            if model_time == expected_time and day_of_week == expected_day:
                correct_0shot += 1
            
            # Print the formatted output with the day of the week
            timestamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            print(f"{example_id}. [{timestamp}] | PROMPT TYPE: {prompt_type} | ANSWER: {{{model_time}}}, {day_of_week} | EXPECTED: {{{expected_time}}}, {expected_day} | REASONING COUNT: {token_count}\n")

            # Write to the text file immediately
            txt_file.write(f"{example_id}. [{timestamp}] | PROMPT TYPE: {prompt_type} | ANSWER: {{{model_time}}}, {day_of_week} | EXPECTED: {{{expected_time}}}, {expected_day} | REASONING COUNT: {token_count}\n")
            
            # Clear the model_response and other temporary variables from memory
            del model_response, model_time, result_entry
            
    # Write the collected results to the JSON file in the desired format
    json.dump({
        "0shot": results_0shot
    }, json_file, indent=4)
    
    # Calculate accuracies
    accuracy_0shot = (correct_0shot / total_0shot) * 100 if total_0shot > 0 else 0
    
    # Write the final accuracy to the text file
    end_time = datetime.datetime.now()
    total_time = end_time - start_time
    txt_file.write(f"\n0-shot prompts: Model guessed {correct_0shot} out of {total_0shot} correctly.\n")
    txt_file.write(f"Accuracy: {accuracy_0shot:.2f}%\n")
    txt_file.write(f"Total time taken: {total_time}\n")

print("Processing complete. Results saved to model_results.txt and model_results.json.")
