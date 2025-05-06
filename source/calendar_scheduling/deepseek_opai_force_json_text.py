import argparse
import json
import datetime
import re
from openai import OpenAI

# Read the API key from a file
with open('/home/rma336/openai_research/deepseek_api_key.txt', 'r') as key_file:
    api_key = key_file.read().strip()  # Use .strip() to remove any extra whitespace or newlines

# Initialize the OpenAI client for Deepseek
client = OpenAI(api_key=api_key, base_url="https://api.deepseek.com")

# Define the JSON schema for the time range output
JSON_SCHEMA = {
    "name": "time_range_schema",  # Add a name for the schema
    "schema": {  # Add the schema field
        "type": "object",
        "properties": {
            "time_range": {
                "type": "string",
                "pattern": "^\\{\\d{2}:\\d{2}:\\d{2}:\\d{2}\\}$"
            }
        },
        "required": ["time_range"],
    }
}

# Load the calendar scheduling examples from the JSON file
with open('calendar_all_1000_prompts.json', 'r') as file:
    calendar_examples = json.load(file)

# Argument parser to select the model
parser = argparse.ArgumentParser(description="Select an model.")
parser.add_argument('--model', type=str, required=True, help="The model ID to use (e.g., 'deepseek-chat').")
args = parser.parse_args()

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
with open('DS-R1-FULL_text_txtresults.txt', 'w') as txt_file, open('DS-R1-FULL_json_txtresults.json', 'w') as json_file:
    start_time = datetime.datetime.now()
    
    for example_id, example in calendar_examples.items():
        for prompt_type in ['prompt_0shot']:
            prompt = example[prompt_type]
            golden_plan = example['golden_plan']

            # Parse golden plan into {HH:MM:HH:MM} format
            expected_time = parse_golden_plan_time(golden_plan)

            # Append the suffix to the prompt
            prompt += "\n\nPlease output the proposed time in the following JSON format:\n{\"time_range\": \"{HH:MM:HH:MM}\"}. For example, if the proposed time is 14:30 to 15:30, the output should be:\n{\"time_range\": \"{14:30:15:30}\"}"

            # Run the model and capture the response
            response = client.chat.completions.create(
                model=args.model,
                messages=[
                    {"role": "system", "content": "You are a helpful assistant."},
                    {"role": "user", "content": prompt}
                ],
                response_format={
                    "type": "json_object",
                    "schema": JSON_SCHEMA
                },
                stream=False
            )

            model_response = response.choices[0].message.content

            def extract_time_range(response):
                """Extracts HH:MM:HH:MM format from the model's raw response and removes leading zeros from single-digit hours."""
                if not response or not isinstance(response, str):  # Check if response is None or not a string
                    return "Invalid response"
                
                # Try to parse as JSON first
                try:
                    json_response = json.loads(response)
                    if 'time_range' in json_response:
                        time_range = json_response['time_range']
                        # Validate the format
                        if re.match(r'^\{\d{1,2}:\d{2}:\d{1,2}:\d{2}\}$', time_range):
                            return time_range
                except json.JSONDecodeError:
                    pass
                
                # Fallback to regex extraction if JSON parsing fails
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
                total_0shot += 1
                if model_time == expected_time:
                    correct_0shot += 1
            # else:
            #     results_5shot.append(result_entry)
            #     total_5shot += 1
            #     if model_time == expected_time:
            #         correct_5shot += 1
            
            # Clear the model_response and other temporary variables from memory
            del model_response, model_time, result_entry
            
    # Write the collected results to the JSON file in the desired format
    json.dump({
        "0shot": results_0shot
        # "5shot": results_5shot
    }, json_file, indent=4)
    
    # Calculate accuracies
    accuracy_0shot = (correct_0shot / total_0shot) * 100 if total_0shot > 0 else 0
    # accuracy_5shot = (correct_5shot / total_5shot) * 100 if total_5shot > 0 else 0
    # total_accuracy = ((correct_0shot + correct_5shot) / (total_0shot + total_5shot)) * 100 if (total_0shot + total_5shot) > 0 else 0
    
    # Write the final accuracy to the text file
    end_time = datetime.datetime.now()
    total_time = end_time - start_time
    txt_file.write(f"\n0-shot prompts: Model guessed {correct_0shot} out of {total_0shot} correctly.\n")
    txt_file.write(f"Accuracy: {accuracy_0shot:.2f}%\n")
    # txt_file.write(f"5-shot prompts: Model guessed {correct_5shot} out of {total_5shot} correctly.\n")
    # txt_file.write(f"Accuracy: {accuracy_5shot:.2f}%\n")
    # txt_file.write(f"Total accuracy: {total_accuracy:.2f}%\n")
    txt_file.write(f"Total time taken: {total_time}\n")

print("Processing complete. Results saved to model_results.txt and model_results.json.")