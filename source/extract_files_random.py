import json

def process_calendar_schedules(input_json_path, target_file_path, json_file_path):
    # Load the calendar scheduling JSON to get the example IDs in original order
    with open(input_json_path, 'r') as json_file:
        data = json.load(json_file)
    
    # Get example IDs in the exact order they appear in the input JSON
    ordered_example_ids = list(data.keys())
    example_ids_set = set(ordered_example_ids)  # For fast lookup
    
    # Read the target text file and create a mapping of example IDs to lines
    with open(target_file_path, 'r') as target_file:
        lines = target_file.readlines()
    
    # Create mapping of example ID to line
    text_file_mapping = {}
    extra_lines = []
    
    for line in lines:
        stripped_line = line.strip()
        if '.' in stripped_line:
            line_example_id = stripped_line.split('.')[0]
            if line_example_id in example_ids_set:
                text_file_mapping[line_example_id] = line
            else:
                extra_lines.append(line)
        else:
            extra_lines.append(line)
    
    # Reconstruct text file lines in the original order
    ordered_matching_lines = []
    for example_id in ordered_example_ids:
        if example_id in text_file_mapping:
            ordered_matching_lines.append(text_file_mapping[example_id])
    
    # Write the filtered text file back in original order
    with open(target_file_path, 'w') as target_file:
        target_file.writelines(ordered_matching_lines + extra_lines)
    print(f"Updated text file with {len(ordered_matching_lines)} matching lines in original order.")
    
    # Process the JSON results file
    with open(json_file_path, 'r') as json_file:
        json_data = json.load(json_file)
    
    # Create mapping of example ID to entry
    json_entries_mapping = {entry["count"]: entry for entry in json_data["0shot"]}
    
    # Filter and order the entries according to the input JSON
    filtered_ordered_entries = []
    for example_id in ordered_example_ids:
        if example_id in json_entries_mapping:
            filtered_ordered_entries.append(json_entries_mapping[example_id])
    
    json_data["0shot"] = filtered_ordered_entries
    
    # Write the filtered JSON back
    with open(json_file_path, 'w') as json_file:
        json.dump(json_data, json_file, indent=4)
    print(f"Updated JSON file with {len(filtered_ordered_entries)} matching entries in original order.")

# Define file paths
input_json_path = 'data/meeting_planning_100.json'
target_file_path = 'source/meeting_planning/1000_0shot_text_outputs/O3-M-25-01-31_forceJSON_text_meeting_results.txt'
json_file_path = 'source/meeting_planning/1000_0shot_text_outputs/O3-M-25-01-31_forceJSON_text_meeting_results.json'

# Call the function
process_calendar_schedules(input_json_path, target_file_path, json_file_path)