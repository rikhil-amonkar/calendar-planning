#!/usr/bin/env python3
import json
from itertools import permutations

# Helper functions for time conversion
def time_to_minutes(t):
    # t is string in "H:MM" 24-hour (e.g., "9:00", "16:15")
    h, m = t.split(":")
    return int(h)*60 + int(m)

def minutes_to_time(m):
    # returns time string in H:MM format (no leading zero for hour)
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

# Travel times provided (in minutes). They are directional.
travel_times = {
    "Bayview": {
        "Nob Hill": 20,
        "Union Square": 17,
        "Chinatown": 18,
        "The Castro": 20,
        "Presidio": 31,
        "Pacific Heights": 23,
        "Russian Hill": 23,
    },
    "Nob Hill": {
        "Bayview": 19,
        "Union Square": 7,
        "Chinatown": 6,
        "The Castro": 17,
        "Presidio": 17,
        "Pacific Heights": 8,
        "Russian Hill": 5,
    },
    "Union Square": {
        "Bayview": 15,
        "Nob Hill": 9,
        "Chinatown": 7,
        "The Castro": 19,
        "Presidio": 24,
        "Pacific Heights": 15,
        "Russian Hill": 13,
    },
    "Chinatown": {
        "Bayview": 22,
        "Nob Hill": 8,
        "Union Square": 7,
        "The Castro": 22,
        "Presidio": 19,
        "Pacific Heights": 10,
        "Russian Hill": 7,
    },
    "The Castro": {
        "Bayview": 19,
        "Nob Hill": 16,
        "Union Square": 19,
        "Chinatown": 20,
        "Presidio": 20,
        "Pacific Heights": 16,
        "Russian Hill": 18,
    },
    "Presidio": {
        "Bayview": 31,
        "Nob Hill": 18,
        "Union Square": 22,
        "Chinatown": 21,
        "The Castro": 21,
        "Pacific Heights": 11,
        "Russian Hill": 14,
    },
    "Pacific Heights": {
        "Bayview": 22,
        "Nob Hill": 8,
        "Union Square": 12,
        "Chinatown": 11,
        "The Castro": 16,
        "Presidio": 11,
        "Russian Hill": 7,
    },
    "Russian Hill": {
        "Bayview": 23,
        "Nob Hill": 5,
        "Union Square": 11,
        "Chinatown": 9,
        "The Castro": 21,
        "Presidio": 14,
        "Pacific Heights": 7,
    },
}

# Meeting constraints for each friend
meetings = {
    "Paul": {
        "location": "Nob Hill",
        "avail_start": time_to_minutes("16:15"),
        "avail_end": time_to_minutes("21:15"),
        "min_duration": 60
    },
    "Carol": {
        "location": "Union Square",
        "avail_start": time_to_minutes("18:00"),
        "avail_end": time_to_minutes("20:15"),
        "min_duration": 120
    },
    "Patricia": {
        "location": "Chinatown",
        "avail_start": time_to_minutes("20:00"),
        "avail_end": time_to_minutes("21:30"),
        "min_duration": 75
    },
    "Karen": {
        "location": "The Castro",
        "avail_start": time_to_minutes("17:00"),
        "avail_end": time_to_minutes("19:00"),
        "min_duration": 45
    },
    "Nancy": {
        "location": "Presidio",
        "avail_start": time_to_minutes("11:45"),
        "avail_end": time_to_minutes("22:00"),
        "min_duration": 30
    },
    "Jeffrey": {
        "location": "Pacific Heights",
        "avail_start": time_to_minutes("20:00"),
        "avail_end": time_to_minutes("20:45"),
        "min_duration": 45
    },
    "Matthew": {
        "location": "Russian Hill",
        "avail_start": time_to_minutes("15:45"),
        "avail_end": time_to_minutes("21:45"),
        "min_duration": 75
    }
}

# Starting conditions
start_location = "Bayview"
start_time = time_to_minutes("9:00")

# Global best itinerary (maximal number of meetings scheduled)
best_itinerary = []
best_count = 0

def travel_time(from_loc, to_loc):
    # Return travel time from from_loc to to_loc.
    if from_loc in travel_times and to_loc in travel_times[from_loc]:
        return travel_times[from_loc][to_loc]
    # If not found, return a large value (should not occur)
    return 999

def dfs(current_location, current_time, remaining, itinerary):
    global best_itinerary, best_count
    # If no remaining meetings, update best if this itinerary is better.
    if len(itinerary) > best_count:
        best_count = len(itinerary)
        best_itinerary = itinerary.copy()
    # Try scheduling each remaining meeting
    for person in list(remaining):
        meet = meetings[person]
        destination = meet["location"]
        # Travel from current_location to destination:
        t_travel = travel_time(current_location, destination)
        arrival_time = current_time + t_travel
        # Wait if arrive before available start:
        meeting_start = max(arrival_time, meet["avail_start"])
        meeting_end = meeting_start + meet["min_duration"]
        # Check if meeting can be held within availability:
        if meeting_end <= meet["avail_end"]:
            # Schedule the meeting
            new_itinerary_entry = {
                "action": "meet",
                "location": destination,
                "person": person,
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            }
            new_itinerary = itinerary + [new_itinerary_entry]
            new_remaining = remaining.copy()
            new_remaining.remove(person)
            dfs(destination, meeting_end, new_remaining, new_itinerary)
    # Also update best if current itinerary is better than best so far.
    if len(itinerary) > best_count:
        best_count = len(itinerary)
        best_itinerary = itinerary.copy()

# We'll try all orders by search. Start recursion with all meetings available.
all_persons = set(meetings.keys())
dfs(start_location, start_time, all_persons, [])

# Prepare output JSON dictionary
output = {
    "itinerary": best_itinerary
}

print(json.dumps(output, indent=2))