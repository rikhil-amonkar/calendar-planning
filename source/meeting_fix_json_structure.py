import json
from datetime import datetime, timedelta

def parse_time_range(time_str):
    """Parse time range string like '2:45PM to 5:30PM' into start and end times"""
    start_str, end_str = time_str.split(' to ')
    return start_str.strip(), end_str.strip()

def extract_meeting_events(golden_schedule):
    """Extract only the 'meet' actions from the golden schedule"""
    return [event for event in golden_schedule if event['action'] == 'meet']

def find_person_for_meeting(constraints, location, start_time):
    """Find the person associated with a meeting at given location and time"""
    for constraint in constraints:
        if len(constraint) >= 4 and isinstance(constraint[0], str) and constraint[0] not in location:
            # This looks like a person constraint (name is first element)
            person, constraint_location, time_range, _ = constraint[:4]
            if constraint_location == location:
                constraint_start, _ = parse_time_range(time_range)
                if constraint_start == start_time:
                    return person
    return None

def transform_entry(original_entry, person_data):
    """Transform a single entry from the original format to the new format"""
    example_id = original_entry['example_id']
    person_info = person_data.get(example_id, {})
    
    # Process expected time (golden schedule)
    expected_itinerary = []
    golden_meetings = extract_meeting_events(original_entry['golden_schedule'])
    
    for meeting in golden_meetings:
        location = meeting['location']
        start_time = meeting['time']
        duration = meeting['duration']
        
        # Calculate end time from start time and duration
        start_dt = datetime.strptime(start_time, "%I:%M%p")
        end_dt = start_dt + timedelta(minutes=duration)
        end_time = end_dt.strftime("%I:%M%p").lstrip('0')
        
        # Find person for this meeting
        person = find_person_for_meeting(
            person_info.get('constraints', []),
            location,
            start_time
        )
        
        expected_itinerary.append({
            "action": "meet",
            "location": location,
            "person": person or "Unknown",
            "start_time": start_time,
            "end_time": end_time
        })
    
    return {
        "final_program_time": {
            "itinerary": "None"
        },
        "expected_time": {
            "itinerary": expected_itinerary
        },
        "raw_model_response": original_entry.get('model_response', ''),
        "count": example_id
    }

def transform_data(original_data, person_data):
    """Transform the entire dataset"""
    transformed = {}
    
    for prompt_type, entries in original_data['results'].items():
        transformed[prompt_type] = [
            transform_entry(entry, person_data)
            for entry in entries
        ]
    
    return transformed

def main():
    # Load the original data
    with open('meet_test_json.json', 'r') as f:
        original_data = json.load(f)
    
    # Load the person data
    with open('../data/meeting_planning_100.json', 'r') as f:
        person_data = json.load(f)
    
    # Transform the data
    transformed_data = transform_data(original_data, person_data)
    
    # Save the transformed data
    with open('meet_new_json.json', 'w') as f:
        json.dump(transformed_data, f, indent=2)
    
    print("Transformation complete. Data saved to transformed_data.json")

if __name__ == "__main__":
    main()