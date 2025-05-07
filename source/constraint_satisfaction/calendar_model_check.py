import os
import json
import re

def load_constraint_dicts(folder_path):
    """Load all constraint dictionaries from files in the given folder."""
    constraint_dicts = {}
    for filename in os.listdir(folder_path):
        if filename.endswith(".json") and "calendar_scheduling_example_" in filename:
            with open(os.path.join(folder_path, filename), 'r') as file:
                constraint_dicts[filename] = json.load(file)
    print(constraint_dicts)
    return constraint_dicts

def load_model_responses(json_file_path):
    """Load model responses from the provided JSON file."""
    with open(json_file_path, 'r') as file:
        model_responses = json.load(file)
    return model_responses

def time_to_minutes(time_str):
    """Convert time in military format (HH:MM) to total minutes."""
    time_str = time_str.strip("{}")  # Remove curly braces
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def parse_answer_time(final_time):
    """Parse the answer time from model output string, assuming format: {start_time:end_time}."""
    time_match = re.search(r'(\d{2}:\d{2}):(\d{2}:\d{2})', final_time)
    if time_match:
        start_time = time_match.group(1)
        end_time = time_match.group(2)
        return start_time, end_time
    return None, None

def compare_time_with_constraints(model_start_time, model_end_time, constraint_dict):
    """Compare the model's time with the constraints and calculate the broken constraints."""
    constraints_broken = 0
    total_constraints = 0

    # Loop through allowed, disallowed, preferred, and unpreferred ranges
    for constraint_type in ['allowed_ranges', 'disallowed_ranges', 'preferred_ranges', 'unpreferred_ranges']:
        if constraint_type in constraint_dict:
            total_constraints += len(constraint_dict[constraint_type])  # Count each range in these sections
            for constraint in constraint_dict[constraint_type]:
                if constraint['day'] == "Monday":  # Assuming we're only interested in Monday for simplicity
                    constraint_start = time_to_minutes(str(constraint['start']))
                    constraint_end = time_to_minutes(str(constraint['end']))
                    model_start_minutes = time_to_minutes(str(model_start_time))
                    model_end_minutes = time_to_minutes(str(model_end_time))

                    # Check if model time breaks the constraint (i.e., if the model time does not fit in the allowed range)
                    if (model_start_minutes < constraint_start or model_end_minutes > constraint_end):
                        constraints_broken += 1

    return constraints_broken, total_constraints


def process_files(constraint_dicts_folder, model_responses_file, output_file):
    """Process all files, compare the times, and write results to output_file."""
    # Load the constraint dictionaries and model responses
    constraint_dicts = load_constraint_dicts(constraint_dicts_folder)
    model_responses = load_model_responses(model_responses_file)

    with open(output_file, 'w') as output:
        # Process each constraint dictionary and its corresponding model response
        for constraint_filename, constraint_dict in constraint_dicts.items():
            example_id = re.search(r'calendar_scheduling_example_(\d+)', constraint_filename).group(1)

            # Find the model response corresponding to this example ID
            model_response = None
            for response in model_responses.get("0shot", []):
                if response["count"].endswith(example_id):
                    model_response = response
                    print(model_response)
                    break

            if model_response:
                model_final_time = model_response["final_time"]
                model_start_time, model_end_time = parse_answer_time(model_final_time)
                
                if model_start_time and model_end_time:
                    constraints_broken, total_constraints = compare_time_with_constraints(
                        model_start_time, model_end_time, constraint_dict)

                    # Calculate accuracy (inverse of constraints broken)
                    if total_constraints > 0:
                        accuracy = ((total_constraints - constraints_broken) / total_constraints) * 100
                    else:
                        accuracy = 100.0
                    output.write(f"{constraint_filename} | Model Response: {model_start_time}:{model_end_time} | Total Constraints: {total_constraints} | Constraints Broken: {constraints_broken} out of {total_constraints} | Response Accuracy: {accuracy:.2f}%\n")

if __name__ == "__main__":
    constraint_dicts_folder = "constraint_satisfaction/calendar"  # Replace with the path to the constraint dictionaries folder
    model_responses_folder = "calendar_scheduling/100_random_0shot_text_outputs/O3-M-25-01-31_json_txtresults.json"  # Replace with the path to the model responses folder
    output_file = "constraint_satisfaction/calendar_constraint_results.txt"  # Output file to store the results

    process_files(constraint_dicts_folder, model_responses_folder, output_file)
