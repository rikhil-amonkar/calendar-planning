#!/usr/bin/env python3
import json
import itertools
from datetime import datetime, timedelta

# Helper functions to convert times
def time_to_minutes(t):
    # expects t as "H:MM" in 24-hour format, e.g., "9:00" or "15:30"
    parts = t.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(m):
    # returns H:MM (no leading zero for hour)
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

# Travel times in minutes between locations.
# We'll store them in a dictionary of dictionaries.
travel_times = {
    "Fisherman's Wharf": {
        "Bayview": 26,
        "Golden Gate Park": 25,
        "Nob Hill": 11,
        "Marina District": 9,
        "Embarcadero": 8
    },
    "Bayview": {
        "Fisherman's Wharf": 25,
        "Golden Gate Park": 22,
        "Nob Hill": 20,
        "Marina District": 25,
        "Embarcadero": 19
    },
    "Golden Gate Park": {
        "Fisherman's Wharf": 24,
        "Bayview": 23,
        "Nob Hill": 20,
        "Marina District": 16,
        "Embarcadero": 25
    },
    "Nob Hill": {
        "Fisherman's Wharf": 11,
        "Bayview": 19,
        "Golden Gate Park": 17,
        "Marina District": 11,
        "Embarcadero": 9
    },
    "Marina District": {
        "Fisherman's Wharf": 10,
        "Bayview": 27,
        "Golden Gate Park": 18,
        "Nob Hill": 12,
        "Embarcadero": 14
    },
    "Embarcadero": {
        "Fisherman's Wharf": 6,
        "Bayview": 21,
        "Golden Gate Park": 25,
        "Nob Hill": 10,
        "Marina District": 12
    }
}

# Meeting constraints for each friend.
# Each friend is represented as a dict with keys: name, location, avail_start, avail_end, and min_duration in minutes.
friends = [
    {
        "name": "Thomas",
        "location": "Bayview",
        "avail_start": time_to_minutes("15:30"),
        "avail_end": time_to_minutes("18:30"),
        "min_duration": 120
    },
    {
        "name": "Stephanie",
        "location": "Golden Gate Park",
        "avail_start": time_to_minutes("18:30"),
        "avail_end": time_to_minutes("21:45"),
        "min_duration": 30
    },
    {
        "name": "Laura",
        "location": "Nob Hill",
        "avail_start": time_to_minutes("8:45"),
        "avail_end": time_to_minutes("16:15"),
        "min_duration": 30
    },
    {
        "name": "Betty",
        "location": "Marina District",
        "avail_start": time_to_minutes("18:45"),
        "avail_end": time_to_minutes("21:45"),
        "min_duration": 45
    },
    {
        "name": "Patricia",
        "location": "Embarcadero",
        "avail_start": time_to_minutes("17:30"),
        "avail_end": time_to_minutes("22:00"),
        "min_duration": 45
    }
]

# Starting point and start time
start_location = "Fisherman's Wharf"
start_time = time_to_minutes("9:00")

# We'll check all permutations of the friends to maximize the number of meetings
# For each permutation, simulate the itinerary:
def simulate_itinerary(order):
    itinerary = []
    current_time = start_time
    current_location = start_location

    for friend in order:
        # Travel to friend's location
        if current_location == friend["location"]:
            travel_time = 0
        else:
            # Get travel time from current_location to friend's location
            # Use the travel_times dictionary. It is directional.
            travel_time = travel_times[current_location][friend["location"]]
        current_time += travel_time
        
        # Meeting can only start when friend is available
        meeting_start = max(current_time, friend["avail_start"])
        meeting_end = meeting_start + friend["min_duration"]
        
        # Check if meeting fits in the friend’s availability window
        if meeting_end > friend["avail_end"]:
            # If meeting doesn't fit, itinerary is invalid for this friend order.
            return None
        
        # Append the meeting action to itinerary
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        
        # Update time and location for next step
        current_time = meeting_end
        current_location = friend["location"]
    return itinerary

# Try all permutations, and choose the one that meets the maximum number of meetings.
best_itinerary = None
best_count = 0
best_finish_time = None

for perm in itertools.permutations(friends):
    itinerary = simulate_itinerary(perm)
    if itinerary is not None:
        count = len(itinerary)
        # The finishing time is the end time of the last meeting
        finish_time = time_to_minutes(itinerary[-1]["end_time"])
        if count > best_count or (count == best_count and (best_finish_time is None or finish_time < best_finish_time)):
            best_count = count
            best_finish_time = finish_time
            best_itinerary = itinerary

# Prepare output in the required JSON format.
result = {"itinerary": best_itinerary if best_itinerary is not None else []}

# Print the JSON output.
print(json.dumps(result, indent=2))