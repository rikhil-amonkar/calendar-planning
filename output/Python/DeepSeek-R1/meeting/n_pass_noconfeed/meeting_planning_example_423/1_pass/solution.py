import json

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1]) if len(parts) > 1 else 0
    return hour * 60 + minute

def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    # Define travel times as a nested dictionary
    travel_times = {
        "Presidio": {
            "Richmond District": 7,
            "North Beach": 18,
            "Financial District": 23,
            "Golden Gate Park": 12,
            "Union Square": 22
        },
        "Richmond District": {
            "Presidio": 7,
            "North Beach": 17,
            "Financial District": 22,
            "Golden Gate Park": 9,
            "Union Square": 21
        },
        "North Beach": {
            "Presidio": 17,
            "Richmond District": 18,
            "Financial District": 8,
            "Golden Gate Park": 22,
            "Union Square": 7
        },
        "Financial District": {
            "Presidio": 22,
            "Richmond District": 21,
            "North Beach": 7,
            "Golden Gate Park": 23,
            "Union Square": 9
        },
        "Golden Gate Park": {
            "Presidio": 11,
            "Richmond District": 7,
            "North Beach": 24,
            "Financial District": 26,
            "Union Square": 22
        },
        "Union Square": {
            "Presidio": 24,
            "Richmond District": 20,
            "North Beach": 10,
            "Financial District": 9,
            "Golden Gate Park": 22
        }
    }
    
    # Define friends in the order we plan to meet them
    friends_in_order = [
        {"name": "Brian", "location": "Financial District", "start": "9:45", "end": "21:45", "min_duration": 15},
        {"name": "Elizabeth", "location": "Golden Gate Park", "start": "8:45", "end": "21:30", "min_duration": 105},
        {"name": "Jason", "location": "Richmond District", "start": "13:00", "end": "20:45", "min_duration": 90},
        {"name": "Laura", "location": "Union Square", "start": "14:15", "end": "19:30", "min_duration": 75},
        {"name": "Melissa", "location": "North Beach", "start": "18:45", "end": "20:15", "min_duration": 45}
    ]
    
    # Convert friend times to minutes
    for friend in friends_in_order:
        friend["start_min"] = time_to_minutes(friend["start"])
        friend["end_min"] = time_to_minutes(friend["end"])
    
    # Initialize simulation
    current_time = time_to_minutes("9:00")  # Start at Presidio at 9:00 AM
    current_location = "Presidio"
    itinerary = []
    
    # Process each friend in order
    for friend in friends_in_order:
        # Travel to friend's location
        travel_duration = travel_times[current_location][friend["location"]]
        current_time += travel_duration
        
        # Determine meeting start time (wait if necessary)
        meeting_start = max(current_time, friend["start_min"])
        meeting_end = meeting_start + friend["min_duration"]
        
        # Check if meeting is feasible
        if meeting_end > friend["end_min"]:
            # Skip this friend if not feasible
            current_time = meeting_start  # We arrived but couldn't meet
            continue
        
        # Add meeting to itinerary
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        
        # Update current time and location after meeting
        current_time = meeting_end
        current_location = friend["location"]
    
    # Output itinerary as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()