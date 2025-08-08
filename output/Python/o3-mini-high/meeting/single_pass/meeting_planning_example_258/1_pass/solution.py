#!/usr/bin/env python3
import itertools
import json

# Helper function to convert minutes (from midnight) to "H:MM" format (24-hour, no leading zero for hour)
def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Travel times (in minutes) between locations
travel_times = {
    "Embarcadero": {
        "Presidio": 20,
        "Richmond District": 21,
        "Fisherman's Wharf": 6
    },
    "Presidio": {
        "Embarcadero": 20,
        "Richmond District": 7,
        "Fisherman's Wharf": 19
    },
    "Richmond District": {
        "Embarcadero": 19,
        "Presidio": 7,
        "Fisherman's Wharf": 18
    },
    "Fisherman's Wharf": {
        "Embarcadero": 8,
        "Presidio": 17,
        "Richmond District": 18
    }
}

# Meeting constraints for each friend:
# Times are converted to minutes from midnight.
# Betty: Presidio from 10:15 (615) to 21:30 (1290) with a minimum meeting duration of 45 minutes.
# David: Richmond District from 13:00 (780) to 20:15 (1215) with a minimum meeting duration of 90 minutes.
# Barbara: Fisherman's Wharf from 9:15 (555) to 20:15 (1215) with a minimum meeting duration of 120 minutes.
friends = [
    {
        "name": "Betty",
        "location": "Presidio",
        "avail_start": 10 * 60 + 15,  # 10:15 -> 615
        "avail_end": 21 * 60 + 30,    # 21:30 -> 1290
        "duration": 45
    },
    {
        "name": "David",
        "location": "Richmond District",
        "avail_start": 13 * 60 + 0,   # 13:00 -> 780
        "avail_end": 20 * 60 + 15,    # 20:15 -> 1215
        "duration": 90
    },
    {
        "name": "Barbara",
        "location": "Fisherman's Wharf",
        "avail_start": 9 * 60 + 15,   # 9:15 -> 555
        "avail_end": 20 * 60 + 15,    # 20:15 -> 1215
        "duration": 120
    }
]

# Starting parameters
start_location = "Embarcadero"
start_time = 9 * 60  # 9:00AM -> 540 minutes from midnight

# We want to maximize the number of meetings (ideally all three) and finish as early as possible.
best_schedule = None
best_finish_time = float('inf')

# Iterate over all possible orders of meetings
for order in itertools.permutations(friends):
    itinerary = []
    current_time = start_time
    current_location = start_location
    feasible = True

    for friend in order:
        # Travel from current location to friend's location
        travel_time = travel_times[current_location][friend["location"]]
        arrival_time = current_time + travel_time
        
        # Wait if arrived before friend's available start time
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["duration"]
        
        # Check if meeting can be completed before the friend leaves
        if meeting_end > friend["avail_end"]:
            feasible = False
            break
        
        # Add this meeting to the itinerary
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
    
    # If the entire order was feasible and meets all friends, check if it finishes earlier
    if feasible:
        if current_time < best_finish_time:
            best_finish_time = current_time
            best_schedule = itinerary

# Prepare the result as a JSON dictionary
if best_schedule is None:
    result = {"itinerary": []}
else:
    result = {"itinerary": best_schedule}

# Output the result as JSON-formatted string
print(json.dumps(result, indent=2))