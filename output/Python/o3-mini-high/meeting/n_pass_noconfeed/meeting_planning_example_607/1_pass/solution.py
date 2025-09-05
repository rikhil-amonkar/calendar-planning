#!/usr/bin/env python3
import json
from itertools import permutations

# Helper functions to convert time formats.
def time_to_minutes(t):
    # t is a string "H:MM" (24-hour format)
    h, m = t.split(':')
    return int(h) * 60 + int(m)

def minutes_to_time(m):
    h = m // 60
    min_part = m % 60
    return f"{h}:{min_part:02d}"

# Travel times (in minutes) between locations
travel_times = {
    "Sunset District": {
        "Russian Hill": 24,
        "The Castro": 17,
        "Richmond District": 12,
        "Marina District": 21,
        "North Beach": 29,
        "Union Square": 30,
        "Golden Gate Park": 11
    },
    "Russian Hill": {
        "Sunset District": 23,
        "The Castro": 21,
        "Richmond District": 14,
        "Marina District": 7,
        "North Beach": 5,
        "Union Square": 11,
        "Golden Gate Park": 21
    },
    "The Castro": {
        "Sunset District": 17,
        "Russian Hill": 18,
        "Richmond District": 16,
        "Marina District": 21,
        "North Beach": 20,
        "Union Square": 19,
        "Golden Gate Park": 11
    },
    "Richmond District": {
        "Sunset District": 11,
        "Russian Hill": 13,
        "The Castro": 16,
        "Marina District": 9,
        "North Beach": 17,
        "Union Square": 21,
        "Golden Gate Park": 9
    },
    "Marina District": {
        "Sunset District": 19,
        "Russian Hill": 8,
        "The Castro": 22,
        "Richmond District": 11,
        "North Beach": 11,
        "Union Square": 16,
        "Golden Gate Park": 18
    },
    "North Beach": {
        "Sunset District": 27,
        "Russian Hill": 4,
        "The Castro": 22,
        "Richmond District": 18,
        "Marina District": 9,
        "Union Square": 7,
        "Golden Gate Park": 22
    },
    "Union Square": {
        "Sunset District": 26,
        "Russian Hill": 13,
        "The Castro": 19,
        "Richmond District": 20,
        "Marina District": 18,
        "North Beach": 10,
        "Golden Gate Park": 22
    },
    "Golden Gate Park": {
        "Sunset District": 10,
        "Russian Hill": 19,
        "The Castro": 13,
        "Richmond District": 7,
        "Marina District": 16,
        "North Beach": 24,
        "Union Square": 22
    }
}

# Meeting constraints for friends with their available times (in minutes) and required durations.
# Times are represented as minutes from midnight.
friends = [
    {
        "name": "Karen",
        "location": "Russian Hill",
        "available_start": 20 * 60 + 45,  # 20:45
        "available_end": 21 * 60 + 45,    # 21:45
        "duration": 60
    },
    {
        "name": "Jessica",
        "location": "The Castro",
        "available_start": 15 * 60 + 45,  # 15:45
        "available_end": 19 * 60 + 30,    # 19:30
        "duration": 60
    },
    {
        "name": "Matthew",
        "location": "Richmond District",
        "available_start": 7 * 60 + 30,   # 7:30
        "available_end": 15 * 60 + 15,    # 15:15
        "duration": 15
    },
    {
        "name": "Michelle",
        "location": "Marina District",
        "available_start": 10 * 60 + 30,  # 10:30
        "available_end": 18 * 60 + 45,    # 18:45
        "duration": 75
    },
    {
        "name": "Carol",
        "location": "North Beach",
        "available_start": 12 * 60,       # 12:00
        "available_end": 17 * 60,         # 17:00
        "duration": 90
    },
    {
        "name": "Stephanie",
        "location": "Union Square",
        "available_start": 10 * 60 + 45,  # 10:45
        "available_end": 14 * 60 + 15,    # 14:15
        "duration": 30
    },
    {
        "name": "Linda",
        "location": "Golden Gate Park",
        "available_start": 10 * 60 + 45,  # 10:45
        "available_end": 22 * 60,         # 22:00
        "duration": 90
    }
]

# You arrive at Sunset District at 9:00.
start_location = "Sunset District"
start_time = 9 * 60  # 9:00 in minutes

def simulate_schedule_and_end_time(order):
    current_time = start_time
    current_location = start_location
    itinerary = []
    for friend in order:
        # Calculate travel time to the friend's meeting location.
        ttime = travel_times[current_location][friend["location"]]
        arrival_time = current_time + ttime
        # Wait if you arrive before the friend is available.
        meeting_start = max(arrival_time, friend["available_start"])
        meeting_end = meeting_start + friend["duration"]
        # Check if the meeting can finish before the friend leaves.
        if meeting_end <= friend["available_end"]:
            itinerary.append({
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            })
            # Update your current time and location after a successful meeting.
            current_time = meeting_end
            current_location = friend["location"]
    return itinerary, current_time

# Brute force search over all permutations of friends to maximize number of meetings.
best_itinerary = []
best_count = 0
best_finish_time = float('inf')

for perm in permutations(friends):
    itinerary, finish_time = simulate_schedule_and_end_time(perm)
    count = len(itinerary)
    # Prefer itineraries that allow meeting more friends and finish earlier.
    if count > best_count or (count == best_count and finish_time < best_finish_time):
        best_count = count
        best_finish_time = finish_time
        best_itinerary = itinerary
    # Early exit if we can meet all friends.
    if best_count == len(friends):
        # We don't break immediately to ensure we pick an optimal (earliest finishing) among full schedules.
        pass

# Prepare output as a JSON-formatted dictionary.
output = {
    "itinerary": best_itinerary
}

# Print the JSON output.
print(json.dumps(output, indent=2))