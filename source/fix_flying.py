import json

def remove_flying_entries(json_data):
    # Loop through the entries in the '0shot' list
    for entry in json_data['0shot']:
        # Filter out any "flying" fields in both final_program_time and expected_time
        entry['final_program_time']['itinerary'] = [
            item for item in entry['final_program_time']['itinerary'] if 'flying' not in item
        ]
        entry['expected_time']['itinerary'] = [
            item for item in entry['expected_time']['itinerary'] if 'flying' not in item
        ]
    return json_data

def process_json(input_file, output_file):
    # Load the JSON data from the input file
    with open(input_file, 'r') as infile:
        json_data = json.load(infile)

    # Process the JSON data to remove "flying" entries
    cleaned_json = remove_flying_entries(json_data)

    # Write the cleaned JSON data to the output file
    with open(output_file, 'w') as outfile:
        json.dump(cleaned_json, outfile, indent=2)

    print(f"Processed JSON saved to {output_file}")

# Example usage
input_file = "test_help.json"
output_file = "test_help_cleaned.json"

process_json(input_file, output_file)
