#!/usr/bin/env python3
import json
import copy

# Helper function: convert time string "H:MM" to minutes from midnight
def time_to_minutes(time_str):
    parts = time_str.split(":")
    return int(parts[0]) * 60 + int(parts[1])

# Helper function: convert minutes from midnight to "H:MM" (24-hour format, no leading zero for hour)
def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Travel times in minutes dictionary between locations
travel_times = {
    "Pacific Heights": {
        "Nob Hill": 8,
        "Russian Hill": 7,
        "The Castro": 16,
        "Sunset District": 21,
        "Haight-Ashbury": 11
    },
    "Nob Hill": {
        "Pacific Heights": 8,
        "Russian Hill": 5,
        "The Castro": 17,
        "Sunset District": 25,
        "Haight-Ashbury": 13
    },
    "Russian Hill": {
        "Pacific Heights": 7,
        "Nob Hill": 5,
        "The Castro": 21,
        "Sunset District": 23,
        "Haight-Ashbury": 17
    },
    "The Castro": {
        "Pacific Heights": 16,
        "Nob Hill": 16,
        "Russian Hill": 18,
        "Sunset District": 17,
        "Haight-Ashbury": 6
    },
    "Sunset District": {
        "Pacific Heights": 21,
        "Nob Hill": 27,
        "Russian Hill": 24,
        "The Castro": 17,
        "Haight-Ashbury": 15
    },
    "Haight-Ashbury": {
        "Pacific Heights": 12,
        "Nob Hill": 15,
        "Russian Hill": 17,
        "The Castro": 6,
        "Sunset District": 15
    }
}

# Define the meeting constraints as a list of friend dicts
# Times in minutes from midnight.
friends = [
    {
        "name": "Ronald",
        "location": "Nob Hill",
        "avail_start": time_to_minutes("10:00"),
        "avail_end": time_to_minutes("17:00"),
        "min_meeting": 105
    },
    {
        "name": "Sarah",
        "location": "Russian Hill",
        "avail_start": time_to_minutes("7:15"),
        "avail_end": time_to_minutes("9:30"),
        "min_meeting": 45
    },
    {
        "name": "Helen",
        "location": "The Castro",
        "avail_start": time_to_minutes("13:30"),
        "avail_end": time_to_minutes("17:00"),
        "min_meeting": 120
    },
    {
        "name": "Joshua",
        "location": "Sunset District",
        "avail_start": time_to_minutes("14:15"),
        "avail_end": time_to_minutes("19:30"),
        "min_meeting": 90
    },
    {
        "name": "Margaret",
        "location": "Haight-Ashbury",
        "avail_start": time_to_minutes("10:15"),
        "avail_end": time_to_minutes("22:00"),
        "min_meeting": 60
    }
]

# Starting conditions
start_location = "Pacific Heights"
start_time = time_to_minutes("9:00")

# We'll perform a recursive search over all possible orders (subsets) of meetings that satisfy constraints.
best_itinerary = []
max_meetings = 0

def search(current_location, current_time, remaining_friends, itinerary):
    global best_itinerary, max_meetings

    # Update best if current itinerary has more meetings
    if len(itinerary) > max_meetings:
        max_meetings = len(itinerary)
        best_itinerary = copy.deepcopy(itinerary)
    
    # Try to meet each remaining friend in turn 
    for i, friend in enumerate(remaining_friends):
        # Determine travel time from current location to friend's location
        if current_location not in travel_times or friend["location"] not in travel_times[current_location]:
            continue
        t_travel = travel_times[current_location][friend["location"]]
        arrival_time = current_time + t_travel
        # Wait until the friend's availability start if arrived early
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["min_meeting"]
        # Check if meeting can finish before friend's avail_end.
        if meeting_end <= friend["avail_end"]:
            # Create meeting event
            meeting_event = {
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            }
            new_itinerary = itinerary + [meeting_event]
            # Build new remaining friends list
            new_remaining = remaining_friends[:i] + remaining_friends[i+1:]
            # Recurse from friend's location and meeting_end as the new time
            search(friend["location"], meeting_end, new_remaining, new_itinerary)

# Start the recursive search from starting location and time with all friends available
search(start_location, start_time, friends, [])

# Prepare the result in the required JSON format.
result = {"itinerary": best_itinerary}

# Output the result as JSON.
print(json.dumps(result, indent=2))