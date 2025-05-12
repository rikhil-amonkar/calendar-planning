import re
import json
import ast

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

def update_itinerary_from_text(json_file_path, text_file_path, output_json_file_path):
    # Load the JSON data
    with open(json_file_path, 'r') as json_file:
        json_data = json.load(json_file)
    
    # Read the text file
    with open(text_file_path, 'r') as text_file:
        lines = text_file.readlines()
    
    # Process each line in the text file
    for line in lines:
        # Extract example ID and ANSWER section
        match = re.search(r"trip_planning_example_(\d+).*?ANSWER: (.*?)(?=\s*EXPECTED:)", line)
        if not match:
            continue
            
        example_id = match.group(1)
        answer_str = match.group(2).strip()

        
        # Skip if ANSWER is None
        if answer_str == "None":
            continue
            
        # Try to parse the answer string into a Python object
        try:
            # Clean up the string if needed (remove 'Day Day' duplicates)
            cleaned_str = answer_str.replace("Day Day", "Day")
            itinerary_data = ast.literal_eval(cleaned_str)
        except (ValueError, SyntaxError) as e:
            print(f"Error parsing answer for example {example_id}: {e}")
            continue
            
        # Find matching entry in JSON
        if "0shot" in json_data and isinstance(json_data["0shot"], list):
            for entry in json_data["0shot"]:
                if not isinstance(entry, dict):
                    continue

                if entry.get('count', '').endswith(f"trip_planning_example_{example_id}"):
                    print(entry.get('count', ''))
                    print(f"Updating itinerary for example {example_id}")
                    if entry.get('final_program_time', {}).get('itinerary') == 'None':
                        # Format the itinerary data properly
                        formatted_itinerary = []
                        for item in itinerary_data:
                            if 'day_range' in item:
                                formatted_item = {
                                    "day_range": item['day_range'],
                                    "place": item['place']
                                }
                            elif 'flying' in item:
                                formatted_item = {
                                    "flying": item['flying'],
                                    "from": item['from'],
                                    "to": item['to']
                                }
                            formatted_itinerary.append(formatted_item)

                        entry['final_program_time']['itinerary'] = formatted_itinerary
                        break
    
    # Remove flying entries after updating the itinerary
    cleaned_json = remove_flying_entries(json_data)
    
    # Save the updated JSON with flying entries removed
    with open(output_json_file_path, 'w') as json_file:
        json.dump(cleaned_json, json_file, indent=2)

    print(f"Processed JSON saved to {output_json_file_path}")

# Example usage
input_json_file = 'trip_planning/100_random_0shot_code_outputs/DS-R1-DL-8B_code_trip_results.json'
text_file = 'trip_planning/100_random_0shot_code_outputs/DS-R1-DL-8B_code_trip_results.txt'
output_json_file = input_json_file

update_itinerary_from_text(input_json_file, text_file, output_json_file)
