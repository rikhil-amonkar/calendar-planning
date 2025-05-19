#!/usr/bin/env python3
import json
from copy import deepcopy

# Helper functions to convert times (in minutes) to string and vice versa.
def time_to_str(minutes):
    # minutes is an integer count since midnight.
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def str_to_time(time_str):
    # time_str format "H:MM" or "HH:MM"
    parts = time_str.split(":")
    return int(parts[0]) * 60 + int(parts[1])

# Define friend meeting constraints as a list of dictionaries.
# Each friend: name, location, avail_start, avail_end and minimum meeting duration in minutes.
friends = [
    {"name": "Joshua", "location": "Embarcadero", "avail_start": str_to_time("9:45"),  "avail_end": str_to_time("18:00"),  "min_duration": 105},
    {"name": "Jeffrey", "location": "Bayview",    "avail_start": str_to_time("9:45"),  "avail_end": str_to_time("20:15"),  "min_duration": 75},
    {"name": "Charles", "location": "Union Square", "avail_start": str_to_time("10:45"), "avail_end": str_to_time("20:15"),  "min_duration": 120},
    {"name": "Joseph",  "location": "Chinatown",   "avail_start": str_to_time("7:00"),   "avail_end": str_to_time("15:30"),  "min_duration": 60},
    {"name": "Elizabeth", "location": "Sunset District", "avail_start": str_to_time("9:00"), "avail_end": str_to_time("9:45"), "min_duration": 45},
    {"name": "Matthew", "location": "Golden Gate Park", "avail_start": str_to_time("11:00"), "avail_end": str_to_time("19:30"), "min_duration": 45},
    {"name": "Carol",   "location": "Financial District", "avail_start": str_to_time("10:45"), "avail_end": str_to_time("11:15"), "min_duration": 15},
    {"name": "Paul",    "location": "Haight-Ashbury", "avail_start": str_to_time("19:15"), "avail_end": str_to_time("20:30"), "min_duration": 15},
    {"name": "Rebecca", "location": "Mission District", "avail_start": str_to_time("17:00"), "avail_end": str_to_time("21:45"), "min_duration": 45}
]

# Define the travel times between locations as a dictionary of dictionaries.
travel_times = {
    "Marina District": {
        "Embarcadero": 14, "Bayview": 27, "Union Square": 16, "Chinatown": 15, "Sunset District": 19,
        "Golden Gate Park": 18, "Financial District": 17, "Haight-Ashbury": 16, "Mission District": 20
    },
    "Embarcadero": {
        "Marina District": 12, "Bayview": 21, "Union Square": 10, "Chinatown": 7, "Sunset District": 30,
        "Golden Gate Park": 25, "Financial District": 5, "Haight-Ashbury": 21, "Mission District": 20
    },
    "Bayview": {
        "Marina District": 27, "Embarcadero": 19, "Union Square": 18, "Chinatown": 19, "Sunset District": 23,
        "Golden Gate Park": 22, "Financial District": 19, "Haight-Ashbury": 19, "Mission District": 13
    },
    "Union Square": {
        "Marina District": 18, "Embarcadero": 11, "Bayview": 15, "Chinatown": 7, "Sunset District": 27,
        "Golden Gate Park": 22, "Financial District": 9, "Haight-Ashbury": 18, "Mission District": 14
    },
    "Chinatown": {
        "Marina District": 12, "Embarcadero": 5, "Bayview": 20, "Union Square": 7, "Sunset District": 29,
        "Golden Gate Park": 23, "Financial District": 5, "Haight-Ashbury": 19, "Mission District": 17
    },
    "Sunset District": {
        "Marina District": 21, "Embarcadero": 30, "Bayview": 22, "Union Square": 30, "Chinatown": 30,
        "Golden Gate Park": 11, "Financial District": 30, "Haight-Ashbury": 15, "Mission District": 25
    },
    "Golden Gate Park": {
        "Marina District": 16, "Embarcadero": 25, "Bayview": 23, "Union Square": 22, "Chinatown": 23,
        "Sunset District": 10, "Financial District": 26, "Haight-Ashbury": 7, "Mission District": 17
    },
    "Financial District": {
        "Marina District": 15, "Embarcadero": 4, "Bayview": 19, "Union Square": 9, "Chinatown": 5,
        "Sunset District": 30, "Golden Gate Park": 23, "Haight-Ashbury": 19, "Mission District": 17
    },
    "Haight-Ashbury": {
        "Marina District": 17, "Embarcadero": 20, "Bayview": 18, "Union Square": 19, "Chinatown": 19,
        "Sunset District": 15, "Golden Gate Park": 7, "Financial District": 21, "Mission District": 11
    },
    "Mission District": {
        "Marina District": 19, "Embarcadero": 19, "Bayview": 14, "Union Square": 15, "Chinatown": 16,
        "Sunset District": 24, "Golden Gate Park": 17, "Financial District": 15, "Haight-Ashbury": 12
    }
}

# Global variable to track best solution.
best_itinerary = None
best_count = 0

def dfs(current_location, current_time, visited, itinerary):
    global best_itinerary, best_count
    # For the current state, try to visit any not yet visited friend.
    found_next = False
    for i, friend in enumerate(friends):
        if friend["name"] in visited:
            continue
        # Travel from current_location to friend's meeting location.
        if current_location not in travel_times or friend["location"] not in travel_times[current_location]:
            continue  # if travel time not defined, skip.
        travel_duration = travel_times[current_location][friend["location"]]
        arrival_time = current_time + travel_duration
        # The meeting cannot start before friend's available start.
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["min_duration"]
        # Check if meeting can finish before friend's available end.
        if meeting_end <= friend["avail_end"]:
            # Mark friend as visited and add the meeting to itinerary.
            new_itinerary = deepcopy(itinerary)
            new_itinerary.append({
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": time_to_str(meeting_start),
                "end_time": time_to_str(meeting_end)
            })
            new_visited = visited.copy()
            new_visited.add(friend["name"])
            # Recurse with updated time and location.
            dfs(friend["location"], meeting_end, new_visited, new_itinerary)
            found_next = True
    # If no next meeting possible, update best solution if current itinerary is better.
    if not found_next:
        if len(itinerary) > best_count:
            best_count = len(itinerary)
            best_itinerary = itinerary

def main():
    global best_itinerary
    # Start at Marina District at 9:00AM.
    start_location = "Marina District"
    start_time = str_to_time("9:00")
    dfs(start_location, start_time, set(), [])
    # Prepare the output JSON structure.
    output = {"itinerary": best_itinerary if best_itinerary is not None else []}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()