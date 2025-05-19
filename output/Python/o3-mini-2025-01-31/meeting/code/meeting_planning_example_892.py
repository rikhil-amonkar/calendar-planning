#!/usr/bin/env python3
import json
import copy

# Helper functions to convert time
def str_to_minutes(timestr):
    # timestr assumed format "H:MM" or "HH:MM"
    parts = timestr.split(":")
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times dictionary: travel_times[from][to] (all given in minutes)
travel_times = {
    "Marina District": {
        "Bayview": 27,
        "Sunset District": 19,
        "Richmond District": 11,
        "Nob Hill": 12,
        "Chinatown": 15,
        "Haight-Ashbury": 16,
        "North Beach": 11,
        "Russian Hill": 8,
        "Embarcadero": 14
    },
    "Bayview": {
        "Marina District": 27,
        "Sunset District": 23,
        "Richmond District": 25,
        "Nob Hill": 20,
        "Chinatown": 19,
        "Haight-Ashbury": 19,
        "North Beach": 22,
        "Russian Hill": 23,
        "Embarcadero": 19
    },
    "Sunset District": {
        "Marina District": 21,
        "Bayview": 22,
        "Richmond District": 12,
        "Nob Hill": 27,
        "Chinatown": 30,
        "Haight-Ashbury": 15,
        "North Beach": 28,
        "Russian Hill": 24,
        "Embarcadero": 30
    },
    "Richmond District": {
        "Marina District": 9,
        "Bayview": 27,
        "Sunset District": 11,
        "Nob Hill": 17,
        "Chinatown": 20,
        "Haight-Ashbury": 10,
        "North Beach": 17,
        "Russian Hill": 13,
        "Embarcadero": 19
    },
    "Nob Hill": {
        "Marina District": 11,
        "Bayview": 19,
        "Sunset District": 24,
        "Richmond District": 14,
        "Chinatown": 6,
        "Haight-Ashbury": 13,
        "North Beach": 8,
        "Russian Hill": 5,
        "Embarcadero": 9
    },
    "Chinatown": {
        "Marina District": 12,
        "Bayview": 20,
        "Sunset District": 29,
        "Richmond District": 20,
        "Nob Hill": 9,
        "Haight-Ashbury": 19,
        "North Beach": 3,
        "Russian Hill": 7,
        "Embarcadero": 5
    },
    "Haight-Ashbury": {
        "Marina District": 17,
        "Bayview": 18,
        "Sunset District": 15,
        "Richmond District": 10,
        "Nob Hill": 15,
        "Chinatown": 19,
        "North Beach": 19,
        "Russian Hill": 17,
        "Embarcadero": 20
    },
    "North Beach": {
        "Marina District": 9,
        "Bayview": 25,
        "Sunset District": 27,
        "Richmond District": 18,
        "Nob Hill": 7,
        "Chinatown": 6,
        "Haight-Ashbury": 18,
        "Russian Hill": 4,
        "Embarcadero": 6
    },
    "Russian Hill": {
        "Marina District": 7,
        "Bayview": 23,
        "Sunset District": 23,
        "Richmond District": 14,
        "Nob Hill": 5,
        "Chinatown": 9,
        "Haight-Ashbury": 17,
        "North Beach": 5,
        "Embarcadero": 8
    },
    "Embarcadero": {
        "Marina District": 12,
        "Bayview": 21,
        "Sunset District": 30,
        "Richmond District": 21,
        "Nob Hill": 10,
        "Chinatown": 7,
        "Haight-Ashbury": 21,
        "North Beach": 5,
        "Russian Hill": 8
    }
}

# Meeting constraints
# Each meeting is represented as a dictionary
# "person": person's name, "location": meeting location,
# "avail_start": available start time in minutes since midnight,
# "avail_end": available end time,
# "duration": required meeting minutes.
meetings = [
    { "person": "Charles", "location": "Bayview", "avail_start": str_to_minutes("11:30"), "avail_end": str_to_minutes("14:30"), "duration": 45 },
    { "person": "Robert", "location": "Sunset District", "avail_start": str_to_minutes("16:45"), "avail_end": str_to_minutes("21:00"), "duration": 30 },
    { "person": "Karen", "location": "Richmond District", "avail_start": str_to_minutes("19:15"), "avail_end": str_to_minutes("21:30"), "duration": 60 },
    { "person": "Rebecca", "location": "Nob Hill", "avail_start": str_to_minutes("16:15"), "avail_end": str_to_minutes("20:30"), "duration": 90 },
    { "person": "Margaret", "location": "Chinatown", "avail_start": str_to_minutes("14:15"), "avail_end": str_to_minutes("19:45"), "duration": 120 },
    { "person": "Patricia", "location": "Haight-Ashbury", "avail_start": str_to_minutes("14:30"), "avail_end": str_to_minutes("20:30"), "duration": 45 },
    { "person": "Mark", "location": "North Beach", "avail_start": str_to_minutes("14:00"), "avail_end": str_to_minutes("18:30"), "duration": 105 },
    { "person": "Melissa", "location": "Russian Hill", "avail_start": str_to_minutes("13:00"), "avail_end": str_to_minutes("19:45"), "duration": 30 },
    { "person": "Laura", "location": "Embarcadero", "avail_start": str_to_minutes("7:45"), "avail_end": str_to_minutes("13:15"), "duration": 105 }
]

# Start location and time
start_location = "Marina District"
start_time = str_to_minutes("9:00")

# Global variable to keep the best itinerary (max meetings)
best_itinerary = []
best_count = 0

# Recursive DFS to explore possible sequences meeting constraints.
def dfs(current_location, current_time, remaining_meetings, itinerary):
    global best_itinerary, best_count
    updated = False
    for i, meeting in enumerate(remaining_meetings):
        # Travel time from current location to meeting location
        travel_time = travel_times[current_location][meeting["location"]]
        arrival_time = current_time + travel_time
        meeting_start = max(arrival_time, meeting["avail_start"])
        meeting_end = meeting_start + meeting["duration"]
        # Check if meeting can be scheduled within availability window.
        if meeting_end <= meeting["avail_end"]:
            # Create meeting event and continue DFS
            event = {
                "action": "meet",
                "location": meeting["location"],
                "person": meeting["person"],
                "start_time": minutes_to_str(meeting_start),
                "end_time": minutes_to_str(meeting_end)
            }
            new_itinerary = itinerary + [event]
            new_remaining = remaining_meetings[:i] + remaining_meetings[i+1:]
            dfs(meeting["location"], meeting_end, new_remaining, new_itinerary)
            updated = True
    # If no further meeting can be added, update best itinerary if count is higher.
    if not updated:
        if len(itinerary) > best_count:
            best_count = len(itinerary)
            best_itinerary = itinerary

# Run DFS starting from initial location and time.
dfs(start_location, start_time, meetings, [])

# Prepare output data
output = {
    "itinerary": best_itinerary
}

# Print result as JSON formatted dictionary.
print(json.dumps(output, indent=2))