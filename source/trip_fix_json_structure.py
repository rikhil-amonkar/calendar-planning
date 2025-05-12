import json

def restructure_json(original_data):
    def remove_flying_entries(itinerary):
        """Recursively remove entries with 'flying', 'from', and 'to' keys."""
        return [
            item for item in itinerary
            if not (isinstance(item, dict) and all(k in item for k in ['flying', 'from', 'to']))
        ]

    restructured = {}
    
    for key in original_data:
        if key not in restructured:
            restructured[key] = []
            
        for example in original_data[key]:
            # Check if example is a dictionary (not a string)
            if isinstance(example, dict):
                # Remove the 'flying', 'from', and 'to' fields from nested itineraries
                if "model_itinerary" in example:
                    example["model_itinerary"] = remove_flying_entries(example["model_itinerary"])
                if "golden_itinerary" in example:
                    example["golden_itinerary"] = remove_flying_entries(example["golden_itinerary"])
                
                # Remove the 'flying', 'from', and 'to' fields if they exist
                example_cleaned = {k: v for k, v in example.items() if k not in ['flying', 'from', 'to']}
                
                new_example = {
                    "final_program_time": {
                        "itinerary": example_cleaned.get("model_itinerary", [])  # Default value as shown in your example
                    },
                    "expected_time": {
                        "itinerary": example_cleaned.get("golden_itinerary", [])
                    },
                    "raw_model_response": example_cleaned.get("model_response", ""),
                    "count": example_cleaned["example_id"]
                }
                restructured[key].append(new_example)
            else:
                # Handle non-dictionary examples if needed
                pass
    
    return restructured

# Example usage:
if __name__ == "__main__":
    # Load your original JSON file
    input_file = 'trip_planning/100_random_0shot_text_outputs/O3-M-25-01-31_forceJSON_text_trip_results.json'
    with open(input_file, 'r') as f:
        original_data = json.load(f)
    
    # Restructure the data
    restructured_data = restructure_json(original_data)
    
    # Save the restructured data to a new file
    with open(input_file, 'w') as f:
        json.dump(restructured_data, f, indent=2)
    
    print("JSON file has been restructured successfully!")



# import json

# # Function to read the original JSON file
# def read_json_file(file_path):
#     with open(file_path, 'r') as file:
#         return json.load(file)

# # Function to save the transformed JSON to a file
# def save_json_file(file_path, data):
#     with open(file_path, 'w') as file:
#         json.dump(data, file, indent=2)

# # Function to restructure the data
# def restructure_data(original_data):
#     new_data = {"0shot": []}
    
#     # Iterate through each example in the 0shot list
#     for example in original_data["0shot"]:
#         new_example = {}
        
#         # Transform 'final_program_time' and insert "None" where necessary
#         if example.get('final_program_time') is not None:
#             if example['final_program_time']:
#                 new_example['final_program_time'] = {
#                     "itinerary": [
#                         {"day_range": entry["day_range"], "place": entry.get("place", "None")} if "place" in entry else entry
#                         for entry in example['final_program_time'] if "flying" not in entry
#                     ]
#                 }
#             else:
#                 new_example['final_program_time'] = {"itinerary": "None"}
#         else:
#             new_example['final_program_time'] = {"itinerary": "None"}
        
#         # Transform 'expected_plan' and insert "None" where necessary
#         if example.get('expected_plan') is not None:
#             if example['expected_plan']:
#                 new_example['expected_time'] = {
#                     "itinerary": [
#                         {"day_range": entry["day_range"], "place": entry.get("place", "None")} if "place" in entry else entry
#                         for entry in example['expected_plan'] if "flying" not in entry
#                     ]
#                 }
#             else:
#                 new_example['expected_time'] = {"itinerary": "None"}
#         else:
#             new_example['expected_time'] = {"itinerary": "None"}
        
#         # Set 'has_error' to true if there's a type_error in the original data
#         new_example["has_error"] = example.get("type_error") is not None
        
#         # Set 'raw_model_response' (this could be from original data, keeping it as is for now)
#         new_example["raw_model_response"] = example.get("full_response", "None")
        
#         # Copy the count from original data
#         new_example["count"] = example.get("count", "None")
        
#         # Add the transformed example to the new data
#         new_data["0shot"].append(new_example)
    
#     return new_data

# # Example usage
# input_file_path = 'trip_planning/100_random_0shot_code_outputs/DS-R1-DL-8B_code_trip_results.json'  # Replace with your actual input file path
# output_file_path = 'trip_planning/100_random_0shot_code_outputs/DS-R1-DL-8B_code_trip_results.json'  # Replace with your actual output file path

# # Read the input file
# original_data = read_json_file(input_file_path)

# # Restructure the data
# transformed_data = restructure_data(original_data)

# # Save the transformed data to the output file
# save_json_file(output_file_path, transformed_data)

# print(f"Transformed data saved to {output_file_path}")

