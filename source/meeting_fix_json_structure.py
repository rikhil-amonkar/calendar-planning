import json

# Function to read the original JSON file
def read_json_file(file_path):
    with open(file_path, 'r') as file:
        return json.load(file)

# Function to save the transformed JSON to a file
def save_json_file(file_path, data):
    with open(file_path, 'w') as file:
        json.dump(data, file, indent=2)

# Function to load the people data
def load_people_data(file_path):
    with open(file_path, 'r') as file:
        return json.load(file)

# Function to restructure the data
def restructure_data(original_data, people_data):
    new_data = {"0shot": []}
    
    # Iterate through each example in the 0shot list
    for example in original_data["0shot"]:
        new_example = {}
        
        # Get the corresponding person data for the example based on "count"
        person_data = people_data.get(example["count"], None)
        
        # Process final_program_plan
        if example.get('final_program_plan') is not None:
            if example['final_program_plan']:
                new_example['final_program_time'] = {
                    "itinerary": []
                }
                for entry in example['final_program_plan']:
                    if entry["action"] == "meet":
                        meeting = {
                            "action": "meet",
                            "location": entry["location"],
                            "person": match_person(entry["location"], entry["time"], person_data),
                            "start_time": entry["time"],
                            "end_time": calculate_end_time(entry["time"], entry["duration"] if "duration" in entry else 0)
                        }
                        new_example['final_program_time']["itinerary"].append(meeting)
            else:
                new_example['final_program_time'] = {"itinerary": "None"}
        else:
            new_example['final_program_time'] = {"itinerary": "None"}
        
        # Process expected_plan similarly
        if example.get('expected_plan') is not None:
            if example['expected_plan']:
                new_example['expected_time'] = {
                    "itinerary": []
                }
                for entry in example['expected_plan']:
                    if entry["action"] == "meet":
                        meeting = {
                            "action": "meet",
                            "location": entry["location"],
                            "person": match_person(entry["location"], entry["time"], person_data),
                            "start_time": entry["time"],
                            "end_time": calculate_end_time(entry["time"], entry["duration"] if "duration" in entry else 0)
                        }
                        new_example['expected_time']["itinerary"].append(meeting)
            else:
                new_example['expected_time'] = {"itinerary": "None"}
        else:
            new_example['expected_time'] = {"itinerary": "None"}
        
        # Set has_error if type_error is not None
        new_example["has_error"] = example.get("type_error") is not None
        
        # Set the raw_model_response
        new_example["raw_model_response"] = example.get("full_response", "None")
        
        # Copy the count from the original data
        new_example["count"] = example.get("count", "None")
        
        # Add the transformed example to the new data
        new_data["0shot"].append(new_example)
    
    return new_data

# Helper function to match person based on location and time
def match_person(location, time, person_data):
    if person_data:
        for constraint in person_data["constraints"]:
            # Check if the location and time match (time may have a range)
            if location == constraint[1] and is_time_in_range(time, constraint[2]):
                return constraint[0]  # Return the person name that matches the location and time
    return "Unknown"  # If no match, return "Unknown"

# Helper function to check if the time is in the range (e.g., "2:45PM to 5:30PM")
def is_time_in_range(time_str, time_range_str):
    # Example: time_str = "2:45PM", time_range_str = "2:45PM to 5:30PM"
    time_range = time_range_str.split(" to ")
    start_time = time_range[0]
    end_time = time_range[1]
    
    # Convert time_str, start_time, and end_time to minutes
    time_minutes = convert_time_to_minutes(time_str)
    start_minutes = convert_time_to_minutes(start_time)
    end_minutes = convert_time_to_minutes(end_time)
    
    return start_minutes <= time_minutes <= end_minutes

# Helper function to calculate end time
def calculate_end_time(start_time_str, duration):
    # Convert the start time string "HH:MMAM/PM" to minutes since midnight
    start_time = convert_time_to_minutes(start_time_str)
    end_time = start_time + duration
    # Convert back the minutes to time format
    return convert_minutes_to_time(end_time)

# Convert time string "HH:MMAM/PM" to minutes since midnight
def convert_time_to_minutes(time_str):
    # Handle 12-hour time format, parsing AM/PM
    hour = int(time_str.split(":")[0])
    minute = int(time_str.split(":")[1][:2])
    period = time_str[-2:]
    
    if period == "PM" and hour != 12:
        hour += 12
    elif period == "AM" and hour == 12:
        hour = 0
    
    return hour * 60 + minute

# Convert minutes since midnight back to time string "H:MMAM/PM" (removes leading zero)
def convert_minutes_to_time(minutes):
    hour = int(minutes // 60)  # Ensure that hour is an integer
    minute = int(minutes % 60)  # Ensure that minute is an integer
    period = "AM" if hour < 12 else "PM"
    
    # Remove the leading zero if hour is less than 10
    if hour == 0:
        hour = 12
    elif hour > 12:
        hour -= 12
    
    return f"{hour}:{minute:02d}{period}"


# Example usage
input_file_path = 'meeting_planning/100_random_0shot_code_outputs/O3-M-25-01-31_code_meeting_results.json'  # Replace with your actual input file path
output_file_path = input_file_path  # Replace with your actual output file path
people_file_path = '../data/meeting_planning_100.json'  # Replace with the file path containing the people data

# Read the input file
original_data = read_json_file(input_file_path)

# Read the people data
people_data = load_people_data(people_file_path)

# Restructure the data
transformed_data = restructure_data(original_data, people_data)

# Save the transformed data to the output file
save_json_file(output_file_path, transformed_data)

print(f"Transformed data saved to {output_file_path}")
