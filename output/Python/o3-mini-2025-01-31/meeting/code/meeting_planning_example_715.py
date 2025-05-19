#!/usr/bin/env python3
import json
import copy

# Utility functions to convert time strings "H:MM" <-> minutes since midnight
def time_to_minutes(t):
    # t is string like "9:00" or "13:30"
    parts = t.split(":")
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(m):
    # Format as H:MM with no leading zero on hour.
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

# Define travel times (in minutes) as nested dictionary.
travel_times = {
    "Presidio": {
        "Marina District": 11,
        "The Castro": 21,
        "Fisherman's Wharf": 19,
        "Bayview": 31,
        "Pacific Heights": 11,
        "Mission District": 26,
        "Alamo Square": 19,
        "Golden Gate Park": 12
    },
    "Marina District": {
        "Presidio": 10,
        "The Castro": 22,
        "Fisherman's Wharf": 10,
        "Bayview": 27,
        "Pacific Heights": 7,
        "Mission District": 20,
        "Alamo Square": 15,
        "Golden Gate Park": 18
    },
    "The Castro": {
        "Presidio": 20,
        "Marina District": 21,
        "Fisherman's Wharf": 24,
        "Bayview": 19,
        "Pacific Heights": 16,
        "Mission District": 7,
        "Alamo Square": 8,
        "Golden Gate Park": 11
    },
    "Fisherman's Wharf": {
        "Presidio": 17,
        "Marina District": 9,
        "The Castro": 27,
        "Bayview": 26,
        "Pacific Heights": 12,
        "Mission District": 22,
        "Alamo Square": 21,
        "Golden Gate Park": 25
    },
    "Bayview": {
        "Presidio": 32,
        "Marina District": 27,
        "The Castro": 19,
        "Fisherman's Wharf": 25,
        "Pacific Heights": 23,
        "Mission District": 13,
        "Alamo Square": 16,
        "Golden Gate Park": 22
    },
    "Pacific Heights": {
        "Presidio": 11,
        "Marina District": 6,
        "The Castro": 16,
        "Fisherman's Wharf": 13,
        "Bayview": 22,
        "Mission District": 15,
        "Alamo Square": 10,
        "Golden Gate Park": 15
    },
    "Mission District": {
        "Presidio": 25,
        "Marina District": 19,
        "The Castro": 7,
        "Fisherman's Wharf": 22,
        "Bayview": 14,
        "Pacific Heights": 16,
        "Alamo Square": 11,
        "Golden Gate Park": 17
    },
    "Alamo Square": {
        "Presidio": 17,
        "Marina District": 15,
        "The Castro": 8,
        "Fisherman's Wharf": 19,
        "Bayview": 16,
        "Pacific Heights": 10,
        "Mission District": 10,
        "Golden Gate Park": 9
    },
    "Golden Gate Park": {
        "Presidio": 11,
        "Marina District": 16,
        "The Castro": 13,
        "Fisherman's Wharf": 24,
        "Bayview": 23,
        "Pacific Heights": 16,
        "Mission District": 17,
        "Alamo Square": 9
    }
}

# Meeting constraints for each friend.
# Each entry: friend: { "location": str, "avail_start": minutes, "avail_end": minutes, "min_duration": minutes }
meetings = {
    "Amanda": {
        "location": "Marina District",
        "avail_start": time_to_minutes("14:45"),  # 2:45 PM
        "avail_end": time_to_minutes("19:30"),    # 7:30 PM
        "min_duration": 105
    },
    "Melissa": {
        "location": "The Castro",
        "avail_start": time_to_minutes("9:30"),
        "avail_end": time_to_minutes("17:00"),
        "min_duration": 30
    },
    "Jeffrey": {
        "location": "Fisherman's Wharf",
        "avail_start": time_to_minutes("12:45"),
        "avail_end": time_to_minutes("18:45"),
        "min_duration": 120
    },
    "Matthew": {
        "location": "Bayview",
        "avail_start": time_to_minutes("10:15"),
        "avail_end": time_to_minutes("13:15"),
        "min_duration": 30
    },
    "Nancy": {
        "location": "Pacific Heights",
        "avail_start": time_to_minutes("17:00"),
        "avail_end": time_to_minutes("21:30"),
        "min_duration": 105
    },
    "Karen": {
        "location": "Mission District",
        "avail_start": time_to_minutes("17:30"),
        "avail_end": time_to_minutes("20:30"),
        "min_duration": 105
    },
    "Robert": {
        "location": "Alamo Square",
        "avail_start": time_to_minutes("11:15"),
        "avail_end": time_to_minutes("17:30"),
        "min_duration": 120
    },
    "Joseph": {
        "location": "Golden Gate Park",
        "avail_start": time_to_minutes("8:30"),
        "avail_end": time_to_minutes("21:15"),
        "min_duration": 105
    }
}

# Starting parameters
start_location = "Presidio"
start_time = time_to_minutes("9:00")

# We'll do a DFS search to try all orders in which meetings can be scheduled feasibly.
best_itinerary = []
best_count = 0

def dfs(current_location, current_time, visited, itinerary):
    global best_itinerary, best_count
    # Update best if current itinerary has more meetings
    if len(itinerary) > best_count:
        best_count = len(itinerary)
        best_itinerary = copy.deepcopy(itinerary)
    # Try all remaining friends.
    for friend, info in meetings.items():
        if friend in visited:
            continue
        # Calculate travel time from current_location to friend's meeting location.
        if current_location not in travel_times or info["location"] not in travel_times[current_location]:
            continue  # no route defined
        travel = travel_times[current_location][info["location"]]
        arrival_time = current_time + travel
        # The meeting can only start when both you have arrived and the friend is available.
        meeting_start = max(arrival_time, info["avail_start"])
        meeting_end = meeting_start + info["min_duration"]
        # Check if meeting can be completed within friend's available window.
        if meeting_end > info["avail_end"]:
            continue  # Cannot meet this friend with required duration.
        # Proceed with this meeting.
        visited.add(friend)
        itinerary.append({
            "action": "meet",
            "location": info["location"],
            "person": friend,
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        dfs(info["location"], meeting_end, visited, itinerary)
        # Backtrack.
        itinerary.pop()
        visited.remove(friend)

# Start DFS from initial state
dfs(start_location, start_time, set(), [])

# Build the result as JSON-formatted dictionary.
result = {"itinerary": best_itinerary}
print(json.dumps(result, indent=2))