#!/usr/bin/env python3
import json
import itertools

# Helper functions to convert time formats
def time_to_minutes(t):
    # t is in "H:MM" or "HH:MM" 24-hour format
    parts = t.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(m):
    # return time in "H:MM" 24-hour format with no leading zero for hours
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

# Define travel times (in minutes) between locations
# Keys: (from, to)
travel_times = {
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "North Beach"): 29,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "North Beach"): 3,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "North Beach"): 5,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Russian Hill"): 4
}

# Meeting constraints for each friend as a dictionary
# Each friend has a name, location, availability window and minimum meeting duration (in minutes)
friends = [
    {"name": "Anthony", "location": "Chinatown", "available_start": time_to_minutes("13:15"), "available_end": time_to_minutes("14:30"), "min_duration": 60},
    {"name": "Rebecca", "location": "Russian Hill", "available_start": time_to_minutes("19:30"), "available_end": time_to_minutes("21:15"), "min_duration": 105},
    {"name": "Melissa", "location": "North Beach", "available_start": time_to_minutes("8:15"),  "available_end": time_to_minutes("13:30"), "min_duration": 105}
]

# Starting condition: You arrive at Sunset District at 9:00AM.
start_location = "Sunset District"
start_time = time_to_minutes("9:00")

def get_travel_time(frm, to):
    # retrieve travel time given from and to. If missing, assume symmetric using provided table.
    if (frm, to) in travel_times:
        return travel_times[(frm, to)]
    elif (to, frm) in travel_times:
        return travel_times[(to, frm)]
    else:
        return 0

# We'll try all permutations of friend meeting order and select the one
# that allows the maximum number of meetings.
best_itinerary = None
max_meetings = 0

for perm in itertools.permutations(friends, len(friends)):
    itinerary = []
    current_time = start_time
    current_location = start_location
    feasible = True

    for friend in perm:
        # Travel to friend's location
        travel = get_travel_time(current_location, friend["location"])
        current_time += travel  # arrival time at friend's location

        # Determine meeting start time: must be at or after friend's available_start.
        meeting_start = max(current_time, friend["available_start"])
        meeting_end = meeting_start + friend["min_duration"]

        # Check if meeting fits within friend's available window
        if meeting_end > friend["available_end"]:
            feasible = False
            break

        # Append meeting to itinerary (record times in H:MM format)
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        
        # Update the current time and location after finishing meeting.
        current_time = meeting_end
        current_location = friend["location"]
    # End for each friend

    if feasible and len(itinerary) > max_meetings:
        best_itinerary = itinerary
        max_meetings = len(itinerary)

# Build the result dictionary as specified.
result = {"itinerary": best_itinerary if best_itinerary is not None else []}

# Output the result as JSON
print(json.dumps(result))