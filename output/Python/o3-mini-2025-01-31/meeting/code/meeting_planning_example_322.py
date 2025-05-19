#!/usr/bin/env python3
import json
from datetime import datetime, timedelta

def minutes_to_time_str(total_minutes):
    # Convert total minutes (from midnight) to hour:minute format, no leading zeros
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours}:{minutes:02d}"

# Travel time matrix in minutes (keys as tuples: (from, to))
travel_times = {
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Presidio"): 17
}

# Participant constraints with their location, availability (in minutes since midnight), and minimum meeting duration (in minutes)
# Times are given in 24-hour time. We'll convert them into minutes from midnight.
def to_minutes(time_str):
    # Expects time_str in "H:MM" or "HH:MM"
    parts = time_str.split(":")
    return int(parts[0]) * 60 + int(parts[1])

participants = {
    "William": {
        "location": "Russian Hill",
        "available_start": to_minutes("18:30"),
        "available_end": to_minutes("20:45"),
        "min_duration": 105
    },
    "Michelle": {
        "location": "Chinatown",
        "available_start": to_minutes("8:15"),
        "available_end": to_minutes("14:00"),
        "min_duration": 15
    },
    "George": {
        "location": "Presidio",
        "available_start": to_minutes("10:30"),
        "available_end": to_minutes("18:45"),
        "min_duration": 30
    },
    "Robert": {
        "location": "Fisherman's Wharf",
        "available_start": to_minutes("9:00"),
        "available_end": to_minutes("13:45"),
        "min_duration": 30
    }
}

# Starting point and time
start_location = "Sunset District"
start_time = to_minutes("9:00")  # 9:00 AM

# We'll define a fixed order that allows us to meet all friends:
# 1. Meet Robert at Fisherman's Wharf
# 2. Meet Michelle at Chinatown
# 3. Meet George at Presidio
# 4. Meet William at Russian Hill
order = ["Robert", "Michelle", "George", "William"]

itinerary = []

current_location = start_location
current_time = start_time

for friend in order:
    info = participants[friend]
    destination = info["location"]
    # Get travel time from current location to destination
    travel_key = (current_location, destination)
    travel_duration = travel_times.get(travel_key, None)
    if travel_duration is None:
        # If not direct in our matrix, try reverse (should not happen for our given data)
        travel_duration = travel_times.get((destination, current_location), 0)
    # Compute arrival time after travel
    arrival_time = current_time + travel_duration
    
    # Meeting can only start when the friend is available.
    meeting_start = max(arrival_time, info["available_start"])
    meeting_end = meeting_start + info["min_duration"]
    
    # Ensure that meeting doesn't exceed available_end (not doing error handling as it's assumed feasible)
    if meeting_end > info["available_end"]:
        raise ValueError(f"Cannot schedule meeting with {friend} within available window.")
    
    # Add meeting action to itinerary
    itinerary.append({
        "action": "meet",
        "location": destination,
        "person": friend,
        "start_time": minutes_to_time_str(meeting_start),
        "end_time": minutes_to_time_str(meeting_end)
    })
    
    # Update current location and time: we leave right after meeting end
    current_location = destination
    current_time = meeting_end

# For William, if we arrive too early before availability, we waited until available_start; however, after meeting George we went to Russian Hill.
# The itinerary already reflects the waiting by scheduling his meeting at max(arrival, available_start).

result = {"itinerary": itinerary}

# Output the result in JSON format
print(json.dumps(result, indent=2))
                    
if __name__ == "__main__":
    pass