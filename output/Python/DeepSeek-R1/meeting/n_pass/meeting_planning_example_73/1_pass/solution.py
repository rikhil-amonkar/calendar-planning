import json

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hours = int(parts[0])
    minutes = int(parts[1])
    return hours * 60 + minutes

def minutes_to_time(minutes_val):
    hours = minutes_val // 60
    minutes = minutes_val % 60
    return f"{hours}:{minutes:02d}"

# Input parameters
start_location = "Russian Hill"
start_time_str = "9:00"
travel_times = {
    ("Russian Hill", "Pacific Heights"): 7,
    ("Pacific Heights", "Russian Hill"): 7
}

friends = [
    {
        "name": "Barbara",
        "location": "Pacific Heights",
        "available_start": "7:15",
        "available_end": "22:00",
        "min_duration": 60
    }
]

# Convert start time to minutes
current_time = time_to_minutes(start_time_str)
current_location = start_location
itinerary = []

# Process each friend (only one in this case)
for friend in friends:
    # Calculate travel time to friend's location
    travel_key = (current_location, friend["location"])
    if travel_key in travel_times:
        travel_duration = travel_times[travel_key]
    else:
        travel_duration = 0  # Default if location not found
    
    # Calculate arrival time at friend's location
    arrival_time = current_time + travel_duration
    
    # Convert friend's availability to minutes
    available_start_min = time_to_minutes(friend["available_start"])
    available_end_min = time_to_minutes(friend["available_end"])
    min_duration = friend["min_duration"]
    
    # Determine meeting window
    meeting_start = max(arrival_time, available_start_min)
    latest_start = available_end_min - min_duration
    
    if meeting_start <= latest_start:
        # Schedule meeting at earliest possible time
        meeting_end = meeting_start + min_duration
        
        # Update current time and location after meeting
        current_time = meeting_end
        current_location = friend["location"]
        
        # Add meeting to itinerary
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })

# Output itinerary as JSON
result = {"itinerary": itinerary}
print(json.dumps(result))