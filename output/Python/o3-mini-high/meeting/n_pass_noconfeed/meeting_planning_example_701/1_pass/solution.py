#!/usr/bin/env python3
import json
import copy

# Convert HH:MM (24-hour) string to minutes after midnight.
def time_to_minutes(tstr):
    parts = tstr.split(':')
    return int(parts[0]) * 60 + int(parts[1])

# Convert minutes since midnight to H:MM format (no leading zero for hour)
def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times dictionary as provided.
travel_times = {
    "Mission District": {
        "The Castro": 7,
        "Nob Hill": 12,
        "Presidio": 25,
        "Marina District": 19,
        "Pacific Heights": 16,
        "Golden Gate Park": 17,
        "Chinatown": 16,
        "Richmond District": 20,
    },
    "The Castro": {
        "Mission District": 7,
        "Nob Hill": 16,
        "Presidio": 20,
        "Marina District": 21,
        "Pacific Heights": 16,
        "Golden Gate Park": 11,
        "Chinatown": 22,
        "Richmond District": 16,
    },
    "Nob Hill": {
        "Mission District": 13,
        "The Castro": 17,
        "Presidio": 17,
        "Marina District": 11,
        "Pacific Heights": 8,
        "Golden Gate Park": 17,
        "Chinatown": 6,
        "Richmond District": 14,
    },
    "Presidio": {
        "Mission District": 26,
        "The Castro": 21,
        "Nob Hill": 18,
        "Marina District": 11,
        "Pacific Heights": 11,
        "Golden Gate Park": 12,
        "Chinatown": 21,
        "Richmond District": 7,
    },
    "Marina District": {
        "Mission District": 20,
        "The Castro": 22,
        "Nob Hill": 12,
        "Presidio": 10,
        "Pacific Heights": 7,
        "Golden Gate Park": 18,
        "Chinatown": 15,
        "Richmond District": 11,
    },
    "Pacific Heights": {
        "Mission District": 15,
        "The Castro": 16,
        "Nob Hill": 8,
        "Presidio": 11,
        "Marina District": 6,
        "Golden Gate Park": 15,
        "Chinatown": 11,
        "Richmond District": 12,
    },
    "Golden Gate Park": {
        "Mission District": 17,
        "The Castro": 13,
        "Nob Hill": 20,
        "Presidio": 11,
        "Marina District": 16,
        "Pacific Heights": 16,
        "Chinatown": 23,
        "Richmond District": 7,
    },
    "Chinatown": {
        "Mission District": 17,
        "The Castro": 22,
        "Nob Hill": 9,
        "Presidio": 19,
        "Marina District": 12,
        "Pacific Heights": 11,
        "Golden Gate Park": 23,
        "Richmond District": 20,
    },
    "Richmond District": {
        "Mission District": 20,
        "The Castro": 16,
        "Nob Hill": 17,
        "Presidio": 7,
        "Marina District": 9,
        "Pacific Heights": 10,
        "Golden Gate Park": 9,
        "Chinatown": 20,
    }
}

# Define each friend's meeting constraints.
# Times are converted to minutes after midnight.
friends = [
    {
        "person": "Lisa",
        "location": "The Castro",
        "avail_start": time_to_minutes("19:15"),
        "avail_end": time_to_minutes("21:15"),
        "min_duration": 120
    },
    {
        "person": "Daniel",
        "location": "Nob Hill",
        "avail_start": time_to_minutes("8:15"),
        "avail_end": time_to_minutes("11:00"),
        "min_duration": 15
    },
    {
        "person": "Elizabeth",
        "location": "Presidio",
        "avail_start": time_to_minutes("21:15"),
        "avail_end": time_to_minutes("22:15"),
        "min_duration": 45
    },
    {
        "person": "Steven",
        "location": "Marina District",
        "avail_start": time_to_minutes("16:30"),
        "avail_end": time_to_minutes("20:45"),
        "min_duration": 90
    },
    {
        "person": "Timothy",
        "location": "Pacific Heights",
        "avail_start": time_to_minutes("12:00"),
        "avail_end": time_to_minutes("18:00"),
        "min_duration": 90
    },
    {
        "person": "Ashley",
        "location": "Golden Gate Park",
        "avail_start": time_to_minutes("20:45"),
        "avail_end": time_to_minutes("21:45"),
        "min_duration": 60
    },
    {
        "person": "Kevin",
        "location": "Chinatown",
        "avail_start": time_to_minutes("12:00"),
        "avail_end": time_to_minutes("19:00"),
        "min_duration": 30
    },
    {
        "person": "Betty",
        "location": "Richmond District",
        "avail_start": time_to_minutes("13:15"),
        "avail_end": time_to_minutes("15:45"),
        "min_duration": 30
    }
]

# Global variables to store the best itinerary (maximizing number of meetings)
best_schedule = []
best_count = 0

# Depth-first search to explore possible meeting orders
def dfs(current_loc, current_time, schedule, remaining):
    global best_schedule, best_count
    
    # Update best schedule if current schedule is longer.
    if len(schedule) > best_count:
        best_schedule = copy.deepcopy(schedule)
        best_count = len(schedule)
    
    # Try adding each remaining friend to the schedule.
    for i, friend in enumerate(remaining):
        # Get travel time from current location to friend's meeting location.
        travel = travel_times[current_loc][friend["location"]]
        arrival_time = current_time + travel
        # The meeting can start no earlier than the later of arrival and friend's available start.
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["min_duration"]
        # Check if we can finish meeting before friend's available end.
        if meeting_end <= friend["avail_end"]:
            meeting = {
                "action": "meet",
                "location": friend["location"],
                "person": friend["person"],
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            }
            new_schedule = schedule + [meeting]
            new_time = meeting_end
            new_loc = friend["location"]
            new_remaining = remaining[:i] + remaining[i+1:]
            dfs(new_loc, new_time, new_schedule, new_remaining)

# Starting conditions:
# You arrive at Mission District at 9:00.
start_loc = "Mission District"
start_time = time_to_minutes("9:00")

# Start DFS search to build meeting itineraries.
dfs(start_loc, start_time, [], friends)

# Build the output dictionary as specified.
output = {"itinerary": best_schedule}

# Print the JSON formatted result.
print(json.dumps(output, indent=2))