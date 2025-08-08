#!/usr/bin/env python3
import json

# Helper functions to convert times to/from minutes
def time_to_minutes(t):
    # expects t in "H:MM" 24-hour format (no leading zero required)
    parts = t.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

# Define travel times between locations (in minutes)
travel_times = {
    "Financial District": {
        "Russian Hill": 10,
        "Sunset District": 31,
        "North Beach": 7,
        "The Castro": 23,
        "Golden Gate Park": 23
    },
    "Russian Hill": {
        "Financial District": 11,
        "Sunset District": 23,
        "North Beach": 5,
        "The Castro": 21,
        "Golden Gate Park": 21
    },
    "Sunset District": {
        "Financial District": 30,
        "Russian Hill": 24,
        "North Beach": 29,
        "The Castro": 17,
        "Golden Gate Park": 11
    },
    "North Beach": {
        "Financial District": 8,
        "Russian Hill": 4,
        "Sunset District": 27,
        "The Castro": 22,
        "Golden Gate Park": 22
    },
    "The Castro": {
        "Financial District": 20,
        "Russian Hill": 18,
        "Sunset District": 17,
        "North Beach": 20,
        "Golden Gate Park": 11
    },
    "Golden Gate Park": {
        "Financial District": 26,
        "Russian Hill": 19,
        "Sunset District": 10,
        "North Beach": 24,
        "The Castro": 13
    }
}

# Define meeting constraints for each friend.
# Times are represented in minutes from midnight.
# You arrive at the Financial District at 9:00 (540 minutes).
friends = [
    {
        "name": "Ronald",
        "location": "Russian Hill",
        "avail_start": time_to_minutes("13:45"),  # 13:45 is 825 minutes
        "avail_end": time_to_minutes("17:15"),    # 17:15 is 1035 minutes
        "min_duration": 105
    },
    {
        "name": "Patricia",
        "location": "Sunset District",
        "avail_start": time_to_minutes("9:15"),   # 9:15 is 555 minutes
        "avail_end": time_to_minutes("22:00"),      # 22:00 is 1320 minutes
        "min_duration": 60
    },
    {
        "name": "Laura",
        "location": "North Beach",
        "avail_start": time_to_minutes("12:30"),    # 12:30 is 750 minutes
        "avail_end": time_to_minutes("12:45"),      # 12:45 is 765 minutes
        "min_duration": 15
    },
    {
        "name": "Emily",
        "location": "The Castro",
        "avail_start": time_to_minutes("16:15"),    # 16:15 is 975 minutes
        "avail_end": time_to_minutes("18:30"),      # 18:30 is 1110 minutes
        "min_duration": 60
    },
    {
        "name": "Mary",
        "location": "Golden Gate Park",
        "avail_start": time_to_minutes("15:00"),    # 15:00 is 900 minutes
        "avail_end": time_to_minutes("16:30"),      # 16:30 is 990 minutes
        "min_duration": 60
    }
]

# Global variable to store best itinerary (maximizing friend count)
best_itinerary = []
best_count = 0

def dfs(current_loc, current_time, visited, itinerary):
    global best_itinerary, best_count, friends, travel_times
    # Update best itinerary if current itinerary has met more friends
    if len(itinerary) > best_count:
        best_count = len(itinerary)
        best_itinerary = itinerary[:]
    
    # Try to schedule a meeting with any friend not yet visited
    for friend in friends:
        if friend["name"] in visited:
            continue
        # Calculate travel time from current location to friend's location
        if current_loc == friend["location"]:
            travel = 0
        else:
            travel = travel_times[current_loc][friend["location"]]
        arrival_time = current_time + travel
        # The meeting can only start when friend is available.
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["min_duration"]
        # Check if meeting can finish before the friend leaves.
        if meeting_end <= friend["avail_end"]:
            event = {
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            }
            dfs(friend["location"], meeting_end, visited + [friend["name"]], itinerary + [event])

# Start DFS from the initial state: at Financial District at 9:00 (540 minutes) with an empty itinerary.
start_location = "Financial District"
start_time = time_to_minutes("9:00")  # 540
dfs(start_location, start_time, [], [])

# The best_itinerary now contains the meeting schedule with the maximum number of friends met.
result = {"itinerary": best_itinerary}

print(json.dumps(result))