#!/usr/bin/env python3
import json
from itertools import chain, permutations

# Convert time in "H:MM" string to minutes from midnight
def time_to_minutes(t):
    parts = t.split(":")
    return int(parts[0]) * 60 + int(parts[1])

# Convert minutes from midnight to "H:MM" string (24-hour, no leading zero for hour)
def minutes_to_time(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

# Travel time matrix (in minutes)
# Matrix format: travel_time[from_location][to_location]
travel_time = {
    "Sunset District": {"North Beach": 29, "Union Square": 30, "Alamo Square": 17},
    "North Beach": {"Sunset District": 27, "Union Square": 7, "Alamo Square": 16},
    "Union Square": {"Sunset District": 26, "North Beach": 10, "Alamo Square": 15},
    "Alamo Square": {"Sunset District": 16, "North Beach": 15, "Union Square": 14}
}

# Define friend meeting constraints
# Times are in minutes from midnight.
friends = {
    "Sarah": {
        "location": "North Beach",
        "available_start": time_to_minutes("16:00"),
        "available_end": time_to_minutes("18:15"),
        "meeting_duration": 60
    },
    "Jeffrey": {
        "location": "Union Square",
        "available_start": time_to_minutes("15:00"),
        "available_end": time_to_minutes("22:00"),
        "meeting_duration": 75
    },
    "Brian": {
        "location": "Alamo Square",
        "available_start": time_to_minutes("16:00"),
        "available_end": time_to_minutes("17:30"),
        "meeting_duration": 75
    }
}

# Starting parameters
start_location = "Sunset District"
start_time = time_to_minutes("9:00")  # 9:00 AM

# Generate all non-empty subsets of the friend names
def all_subsets(iterable):
    s = list(iterable)
    return chain.from_iterable(permutations(s, r) for r in range(1, len(s)+1))

# Evaluate a given itinerary (sequence of friend names) to see if it is feasible.
# Returns a tuple (is_valid, itinerary_steps, finish_time)
def evaluate_itinerary(friend_sequence):
    current_time = start_time
    current_location = start_location
    itinerary_steps = []
    
    for friend in friend_sequence:
        friend_data = friends[friend]
        # Travel from current location to friend's meeting location
        travel = travel_time[current_location][friend_data["location"]]
        arrival_time = current_time + travel
        # The meeting cannot start before friend's available start time.
        meeting_start = max(arrival_time, friend_data["available_start"])
        meeting_end = meeting_start + friend_data["meeting_duration"]
        # Check if meeting ends before friend's available end time.
        if meeting_end > friend_data["available_end"]:
            return (False, [], None)  # Not feasible
        
        # Add step to itinerary:
        itinerary_steps.append({
            "action": "meet",
            "location": friend_data["location"],
            "person": friend,
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        # Update current position and time.
        current_time = meeting_end
        current_location = friend_data["location"]
    
    return (True, itinerary_steps, current_time)

# Explore all possible itineraries (different orderings of friend meetings)
best_itinerary = None
best_count = 0
best_finish_time = None

for friend_order in all_subsets(friends.keys()):
    valid, itinerary_steps, finish_time = evaluate_itinerary(friend_order)
    if valid:
        count = len(itinerary_steps)
        # Choose itinerary that has the maximum number of friend meetings,
        # and in case of tie, the one that finishes earlier.
        if count > best_count or (count == best_count and (best_finish_time is None or finish_time < best_finish_time)):
            best_count = count
            best_finish_time = finish_time
            best_itinerary = itinerary_steps

# Prepare final output as a JSON-formatted dictionary.
output = {"itinerary": best_itinerary if best_itinerary is not None else []}

print(json.dumps(output, indent=2))