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
    for key, dict_list in data.items():
        for idx, item in enumerate(dict_list):
            # Check if item is a dictionary
            if isinstance(item, dict):
                # Extract the 'count' value to use as the filename
                count_value = item.get("count")
                if count_value:
                    # Sanitize the count value to ensure it's a valid filename
                    filename = f"{count_value}.json"
                    filepath = os.path.join(output_folder, filename)

                    # Prepare the output dictionary with the same key (e.g., "0shot")
                    output_data = {key: [item]}

                    # Write the dictionary to a new file
                    with open(filepath, 'w') as out_f:
                        json.dump(output_data, out_f, indent=4)

                    print(f"Saved {filename} to {output_folder}")
                else:
                    print(f"Warning: Missing 'count' in item {idx + 1} (No calendar ID), skipping item.")
            else:
                # Handle non-dictionary items (like strings)
                print(f"Warning: Expected a dictionary, but got {type(item)} with value '{item}'. Skipping item {idx + 1}.")

# Example usage
input_file = 'trip_planning/100_random_0shot_text_outputs/DS-R1-70B-REASON_text_trip_results.json'  # Specify the input file path here
output_folder = '../output/Plan/DeepSeek-R1-Distill-Llama-70B/trip/formatted_output'  # Specify the output folder path here

split_json(input_file, output_folder)


