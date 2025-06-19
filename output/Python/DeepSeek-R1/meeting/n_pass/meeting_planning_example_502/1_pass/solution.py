import json

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hours = int(parts[0])
    minutes = int(parts[1])
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Define travel times as a nested dictionary
travel_times = {
    "Financial District": {
        "Golden Gate Park": 23,
        "Chinatown": 5,
        "Union Square": 9,
        "Fisherman's Wharf": 10,
        "Pacific Heights": 13,
        "North Beach": 7
    },
    "Golden Gate Park": {
        "Financial District": 26,
        "Chinatown": 23,
        "Union Square": 22,
        "Fisherman's Wharf": 24,
        "Pacific Heights": 16,
        "North Beach": 24
    },
    "Chinatown": {
        "Financial District": 5,
        "Golden Gate Park": 23,
        "Union Square": 7,
        "Fisherman's Wharf": 8,
        "Pacific Heights": 10,
        "North Beach": 3
    },
    "Union Square": {
        "Financial District": 9,
        "Golden Gate Park": 22,
        "Chinatown": 7,
        "Fisherman's Wharf": 15,
        "Pacific Heights": 15,
        "North Beach": 10
    },
    "Fisherman's Wharf": {
        "Financial District": 11,
        "Golden Gate Park": 25,
        "Chinatown": 12,
        "Union Square": 13,
        "Pacific Heights": 12,
        "North Beach": 6
    },
    "Pacific Heights": {
        "Financial District": 13,
        "Golden Gate Park": 15,
        "Chinatown": 11,
        "Union Square": 12,
        "Fisherman's Wharf": 13,
        "North Beach": 9
    },
    "North Beach": {
        "Financial District": 8,
        "Golden Gate Park": 22,
        "Chinatown": 6,
        "Union Square": 7,
        "Fisherman's Wharf": 5,
        "Pacific Heights": 8
    }
}

# Define friends in the order to meet them
friends = [
    {
        "name": "Rebecca",
        "location": "Fisherman's Wharf",
        "available_start": time_to_minutes("8:00"),
        "available_end": time_to_minutes("11:15"),
        "min_duration": 30
    },
    {
        "name": "Stephanie",
        "location": "Golden Gate Park",
        "available_start": time_to_minutes("11:00"),
        "available_end": time_to_minutes("15:00"),
        "min_duration": 105
    },
    {
        "name": "Karen",
        "location": "Chinatown",
        "available_start": time_to_minutes("13:45"),
        "available_end": time_to_minutes("16:30"),
        "min_duration": 15
    },
    {
        "name": "Steven",
        "location": "North Beach",
        "available_start": time_to_minutes("14:30"),
        "available_end": time_to_minutes("20:45"),
        "min_duration": 120
    },
    {
        "name": "Brian",
        "location": "Union Square",
        "available_start": time_to_minutes("15:00"),
        "available_end": time_to_minutes("17:15"),
        "min_duration": 30
    }
]

# Starting point
current_location = "Financial District"
current_time = time_to_minutes("9:00")  # 9:00 AM

itinerary = []

for friend in friends:
    # Travel to the friend's location
    travel_time = travel_times[current_location][friend["location"]]
    current_time += travel_time  # Arrival time at friend's location

    # Calculate meeting start and end times
    start_meeting = max(current_time, friend["available_start"])
    end_meeting = start_meeting + friend["min_duration"]
    
    # Check if meeting fits within friend's availability
    if end_meeting > friend["available_end"]:
        # Skip this friend if not possible, but we assume it fits
        continue
    
    # Add meeting to itinerary
    itinerary.append({
        "action": "meet",
        "location": friend["location"],
        "person": friend["name"],
        "start_time": minutes_to_time(start_meeting),
        "end_time": minutes_to_time(end_meeting)
    })
    
    # Update current time and location
    current_time = end_meeting
    current_location = friend["location"]

# Output as JSON
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))