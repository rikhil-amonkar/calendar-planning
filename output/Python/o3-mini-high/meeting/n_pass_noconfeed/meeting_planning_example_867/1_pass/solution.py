#!/usr/bin/env python3
import json

# Helper functions for time conversion
def time_to_minutes(t):
    # t is a string "H:MM"
    parts = t.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(m):
    # Convert minutes to H:MM (24hour, no leading zero for hour)
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

# Define travel times between locations (in minutes)
travel_times = {
    "Haight-Ashbury": {
        "Mission District": 11,
        "Union Square": 19,
        "Pacific Heights": 12,
        "Bayview": 18,
        "Fisherman's Wharf": 23,
        "Marina District": 17,
        "Richmond District": 10,
        "Sunset District": 15,
        "Golden Gate Park": 7,
    },
    "Mission District": {
        "Haight-Ashbury": 12,
        "Union Square": 15,
        "Pacific Heights": 16,
        "Bayview": 14,
        "Fisherman's Wharf": 22,
        "Marina District": 19,
        "Richmond District": 20,
        "Sunset District": 24,
        "Golden Gate Park": 17,
    },
    "Union Square": {
        "Haight-Ashbury": 18,
        "Mission District": 14,
        "Pacific Heights": 15,
        "Bayview": 15,
        "Fisherman's Wharf": 15,
        "Marina District": 18,
        "Richmond District": 20,
        "Sunset District": 27,
        "Golden Gate Park": 22,
    },
    "Pacific Heights": {
        "Haight-Ashbury": 11,
        "Mission District": 15,
        "Union Square": 12,
        "Bayview": 22,
        "Fisherman's Wharf": 13,
        "Marina District": 6,
        "Richmond District": 12,
        "Sunset District": 21,
        "Golden Gate Park": 15,
    },
    "Bayview": {
        "Haight-Ashbury": 19,
        "Mission District": 13,
        "Union Square": 18,
        "Pacific Heights": 23,
        "Fisherman's Wharf": 25,
        "Marina District": 27,
        "Richmond District": 25,
        "Sunset District": 23,
        "Golden Gate Park": 22,
    },
    "Fisherman's Wharf": {
        "Haight-Ashbury": 22,
        "Mission District": 22,
        "Union Square": 13,
        "Pacific Heights": 12,
        "Bayview": 26,
        "Marina District": 9,
        "Richmond District": 18,
        "Sunset District": 27,
        "Golden Gate Park": 25,
    },
    "Marina District": {
        "Haight-Ashbury": 16,
        "Mission District": 20,
        "Union Square": 16,
        "Pacific Heights": 7,
        "Bayview": 27,
        "Fisherman's Wharf": 10,
        "Richmond District": 11,
        "Sunset District": 19,
        "Golden Gate Park": 18,
    },
    "Richmond District": {
        "Haight-Ashbury": 10,
        "Mission District": 20,
        "Union Square": 21,
        "Pacific Heights": 10,
        "Bayview": 27,
        "Fisherman's Wharf": 18,
        "Marina District": 9,
        "Sunset District": 11,
        "Golden Gate Park": 9,
    },
    "Sunset District": {
        "Haight-Ashbury": 15,
        "Mission District": 25,
        "Union Square": 30,
        "Pacific Heights": 21,
        "Bayview": 22,
        "Fisherman's Wharf": 29,
        "Marina District": 21,
        "Richmond District": 12,
        "Golden Gate Park": 11,
    },
    "Golden Gate Park": {
        "Haight-Ashbury": 7,
        "Mission District": 17,
        "Union Square": 22,
        "Pacific Heights": 16,
        "Bayview": 23,
        "Fisherman's Wharf": 24,
        "Marina District": 16,
        "Richmond District": 7,
        "Sunset District": 10,
    },
}

# Define meeting constraints for each friend
# Each friend is represented as a dictionary with:
# "name", "location", "avail_start" (in minutes), "avail_end" (in minutes), "duration" (minutes)
friends = [
    {
        "name": "Elizabeth",
        "location": "Mission District",
        "avail_start": time_to_minutes("10:30"),
        "avail_end": time_to_minutes("20:00"),
        "duration": 90,
    },
    {
        "name": "David",
        "location": "Union Square",
        "avail_start": time_to_minutes("15:15"),
        "avail_end": time_to_minutes("19:00"),
        "duration": 45,
    },
    {
        "name": "Sandra",
        "location": "Pacific Heights",
        "avail_start": time_to_minutes("7:00"),
        "avail_end": time_to_minutes("20:00"),
        "duration": 120,
    },
    {
        "name": "Thomas",
        "location": "Bayview",
        "avail_start": time_to_minutes("19:30"),
        "avail_end": time_to_minutes("20:30"),
        "duration": 30,
    },
    {
        "name": "Robert",
        "location": "Fisherman's Wharf",
        "avail_start": time_to_minutes("10:00"),
        "avail_end": time_to_minutes("15:00"),
        "duration": 15,
    },
    {
        "name": "Kenneth",
        "location": "Marina District",
        "avail_start": time_to_minutes("10:45"),
        "avail_end": time_to_minutes("13:00"),
        "duration": 45,
    },
    {
        "name": "Melissa",
        "location": "Richmond District",
        "avail_start": time_to_minutes("18:15"),
        "avail_end": time_to_minutes("20:00"),
        "duration": 15,
    },
    {
        "name": "Kimberly",
        "location": "Sunset District",
        "avail_start": time_to_minutes("10:15"),
        "avail_end": time_to_minutes("18:15"),
        "duration": 105,
    },
    {
        "name": "Amanda",
        "location": "Golden Gate Park",
        "avail_start": time_to_minutes("7:45"),
        "avail_end": time_to_minutes("18:45"),
        "duration": 15,
    },
]

# Global variables to store the best schedule found
best_schedule = []
best_count = 0
best_finish_time = float('inf')

def backtrack(current_location, current_time, remaining, current_itinerary):
    global best_schedule, best_count, best_finish_time

    # Update best schedule if this itinerary has more meetings 
    # or same number but finishes earlier.
    if len(current_itinerary) > best_count or (len(current_itinerary) == best_count and current_time < best_finish_time):
        best_schedule = current_itinerary.copy()
        best_count = len(current_itinerary)
        best_finish_time = current_time

    # Try to schedule the rest of the meetings in any order
    for i, friend in enumerate(remaining):
        # Calculate travel time from current location to friend's location
        if current_location not in travel_times or friend["location"] not in travel_times[current_location]:
            continue
        travel = travel_times[current_location][friend["location"]]
        arrival_time = current_time + travel
        # Meeting cannot start before friend's availability start; wait if needed.
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["duration"]
        # Check if meeting can be completed within friend's available window
        if meeting_end > friend["avail_end"]:
            continue  # Not feasible to schedule this meeting next
        # Create a schedule entry for this meeting
        meeting_entry = {
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        }
        # Prepare new state after scheduling this meeting
        new_itinerary = current_itinerary + [meeting_entry]
        new_remaining = remaining[:i] + remaining[i+1:]
        # Recurse from the new current location and time
        backtrack(friend["location"], meeting_end, new_remaining, new_itinerary)

# Starting parameters: You arrive at Haight-Ashbury at 9:00AM (which is 540 minutes)
start_location = "Haight-Ashbury"
start_time = time_to_minutes("9:00")

# Begin backtracking search to find the schedule that maximizes meetings
backtrack(start_location, start_time, friends, [])

# Prepare the final output dictionary
result = {"itinerary": best_schedule}

# Output the result as JSON
print(json.dumps(result, indent=2))