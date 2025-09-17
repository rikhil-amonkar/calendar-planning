# import os

# def count_items_non_recursive(directory_path):
#     """Counts the number of items (files and subdirectories) in a directory non-recursively."""
#     try:
#         items = os.listdir(directory_path)
#         return len(items)
#     except FileNotFoundError:
#         return 0  # Directory does not exist

# # Example usage
# directory = "../output/Python/DeepSeek-R1/meeting/n_pass"
# item_count = count_items_non_recursive(directory)
# print(f"Number of items in '{directory}': {item_count}")

import os
import json

def process_json_file(file_path):
    with open(file_path, 'r') as f:
        data = json.load(f)
    
    # Update predicted_output structure by removing "itinerary"
    if "predicted_output" in data and isinstance(data["predicted_output"], dict):
        predicted_output = data["predicted_output"].get("itinerary", [])
        data["predicted_output"] = predicted_output
    
    # Check if predicted_output matches golden_output exactly
    if data.get("predicted_output") == data.get("golden_output"):
        data["is_exact_match"] = True
    else:
        data["is_exact_match"] = False
    
    # Write the updated content back to the file
    with open(file_path, 'w') as f:
        json.dump(data, f, indent=4)

def process_directory(base_directory):
    for root, dirs, files in os.walk(base_directory):
        if "evaluation.json" in files:
            file_path = os.path.join(root, "evaluation.json")
            print(f"Processing {file_path}")
            process_json_file(file_path)

if __name__ == "__main__":
    # Set the base directory path where the example folders are located
    base_directory = '../output/Python/DeepSeek-R1/meeting/n_pass'  # Replace this with the correct path
    process_directory(base_directory)
