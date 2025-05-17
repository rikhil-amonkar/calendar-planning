import json
import os

def split_json(input_file, output_folder):
    # Load the input JSON file
    with open(input_file, 'r') as f:
        data = json.load(f)

    # Check if the output folder exists, create it if not
    if not os.path.exists(output_folder):
        os.makedirs(output_folder)

    # Loop through the dictionary and write each item into a separate JSON file
    for key, items in data.items():
        for idx, item in enumerate(items):
            # Check if item is a dictionary
            if isinstance(item, dict):
                # Extract the 'count' value to use as the filename
                count_value = item.get("count")
                if count_value:
                    # Sanitize the count value to ensure it's a valid filename
                    filename = f"{count_value}.json"
                    filepath = os.path.join(output_folder, filename)

                    # Prepare the output dictionary with the same structure
                    output_data = {
                        key: [{
                            "final_program_time": item.get("final_program_time", {}),
                            "expected_time": item.get("expected_time", {}),
                            "has_error": item.get("has_error", False),
                            "raw_model_response": item.get("raw_model_response", ""),
                            "count": count_value
                        }]
                    }

                    # Write the dictionary to a new file
                    with open(filepath, 'w') as out_f:
                        json.dump(output_data, out_f, indent=4)

                    print(f"Saved {filename} to {output_folder}")
                else:
                    print(f"Warning: Missing 'count' in item {idx + 1}, skipping item.")
            else:
                # Handle non-dictionary items (like strings)
                print(f"Warning: Expected a dictionary, but got {type(item)} with value '{item}'. Skipping item {idx + 1}.")

# Example usage
task = 'calendar'
input_file = f'{task}_scheduling/100_random_0shot_code_outputs_new/O3-M-25-01-31_code_{task}_results.json'
output_folder = f'../output/Python/o3-mini-2025-01-31/{task}/formatted_output/'

split_json(input_file, output_folder)

