#!/usr/bin/env python3
import json

# Helper functions to convert time strings to minutes and vice versa
def time_to_minutes(t):
    # Expects a string in "H:MM" or "HH:MM" format (24-hour)
    h, m = t.split(":")
    return int(h) * 60 + int(m)

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Travel times (in minutes) between districts (directional)
travel_times = {
    "Marina District": {
        "Richmond District": 11,
        "Union Square": 16,
        "Nob Hill": 12,
        "Fisherman's Wharf": 10,
        "Golden Gate Park": 18,
        "Embarcadero": 14,
        "Financial District": 17,
        "North Beach": 11,
        "Presidio": 10
    },
    "Richmond District": {
        "Marina District": 9,
        "Union Square": 21,
        "Nob Hill": 17,
        "Fisherman's Wharf": 18,
        "Golden Gate Park": 9,
        "Embarcadero": 19,
        "Financial District": 22,
        "North Beach": 17,
        "Presidio": 7
    },
    "Union Square": {
        "Marina District": 18,
        "Richmond District": 20,
        "Nob Hill": 9,
        "Fisherman's Wharf": 15,
        "Golden Gate Park": 22,
        "Embarcadero": 11,
        "Financial District": 9,
        "North Beach": 10,
        "Presidio": 24
    },
    "Nob Hill": {
        "Marina District": 11,
        "Richmond District": 14,
        "Union Square": 7,
        "Fisherman's Wharf": 10,
        "Golden Gate Park": 17,
        "Embarcadero": 9,
        "Financial District": 9,
        "North Beach": 8,
        "Presidio": 17
    },
    "Fisherman's Wharf": {
        "Marina District": 9,
        "Richmond District": 18,
        "Union Square": 13,
        "Nob Hill": 11,
        "Golden Gate Park": 25,
        "Embarcadero": 8,
        "Financial District": 11,
        "North Beach": 6,
        "Presidio": 17
    },
    "Golden Gate Park": {
        "Marina District": 16,
        "Richmond District": 7,
        "Union Square": 22,
        "Nob Hill": 20,
        "Fisherman's Wharf": 24,
        "Embarcadero": 25,
        "Financial District": 26,
        "North Beach": 23,
        "Presidio": 11
    },
    "Embarcadero": {
        "Marina District": 12,
        "Richmond District": 21,
        "Union Square": 10,
        "Nob Hill": 10,
        "Fisherman's Wharf": 6,
        "Golden Gate Park": 25,
        "Financial District": 5,
        "North Beach": 5,
        "Presidio": 20
    },
    "Financial District": {
        "Marina District": 15,
        "Richmond District": 21,
        "Union Square": 9,
        "Nob Hill": 8,
        "Fisherman's Wharf": 10,
        "Golden Gate Park": 23,
        "Embarcadero": 4,
        "North Beach": 7,
        "Presidio": 22
    },
    "North Beach": {
        "Marina District": 9,
        "Richmond District": 18,
        "Union Square": 7,
        "Nob Hill": 7,
        "Fisherman's Wharf": 5,
        "Golden Gate Park": 22,
        "Embarcadero": 6,
        "Financial District": 8,
        "Presidio": 17
    },
    "Presidio": {
        "Marina District": 11,
        "Richmond District": 7,
        "Union Square": 22,
        "Nob Hill": 18,
        "Fisherman's Wharf": 19,
        "Golden Gate Park": 12,
        "Embarcadero": 20,
        "Financial District": 23,
        "North Beach": 18
    }
}

# Meeting constraints for each friend
# Each meeting dict contains the friend's name, meeting location,
# available start and end times (in minutes from midnight), and required duration.
meetings = [
    {"person": "Stephanie", "location": "Richmond District", "avail_start": time_to_minutes("16:15"), "avail_end": time_to_minutes("21:30"), "duration": 75},
    {"person": "William", "location": "Union Square", "avail_start": time_to_minutes("10:45"), "avail_end": time_to_minutes("17:30"), "duration": 45},
    {"person": "Elizabeth", "location": "Nob Hill", "avail_start": time_to_minutes("12:15"), "avail_end": time_to_minutes("15:00"), "duration": 105},
    {"person": "Joseph", "location": "Fisherman's Wharf", "avail_start": time_to_minutes("12:45"), "avail_end": time_to_minutes("14:00"), "duration": 75},
    {"person": "Anthony", "location": "Golden Gate Park", "avail_start": time_to_minutes("13:00"), "avail_end": time_to_minutes("20:30"), "duration": 75},
    {"person": "Barbara", "location": "Embarcadero", "avail_start": time_to_minutes("19:15"), "avail_end": time_to_minutes("20:30"), "duration": 75},
    {"person": "Carol", "location": "Financial District", "avail_start": time_to_minutes("11:45"), "avail_end": time_to_minutes("16:15"), "duration": 60},
    {"person": "Sandra", "location": "North Beach", "avail_start": time_to_minutes("10:00"), "avail_end": time_to_minutes("12:30"), "duration": 15},
    {"person": "Kenneth", "location": "Presidio", "avail_start": time_to_minutes("21:15"), "avail_end": time_to_minutes("22:15"), "duration": 45}
]

# Sort meetings by available start time to help guide the search
meetings.sort(key=lambda x: x["avail_start"])

# Backtracking search to compute the optimal meeting schedule.
# The goal is to maximize the number of meetings while satisfying travel times and time windows.
def search(current_time, current_location, remaining_meetings, schedule):
    best_schedule = schedule[:]
    for i, meeting in enumerate(remaining_meetings):
        # Determine travel time from current location to the meeting's location
        if current_location == meeting["location"]:
            travel = 0
        else:
            travel = travel_times[current_location][meeting["location"]]
        arrival_time = current_time + travel
        # The meeting can only start when both you have arrived and the friend is available
        start_time = max(arrival_time, meeting["avail_start"])
        end_time = start_time + meeting["duration"]
        # Check if the meeting can be completed within the friend's available window
        if end_time <= meeting["avail_end"]:
            meeting_details = {
                "action": "meet",
                "location": meeting["location"],
                "person": meeting["person"],
                "start_time": start_time,
                "end_time": end_time
            }
            new_schedule = schedule + [meeting_details]
            # Remove the current meeting from the remaining list
            new_remaining = remaining_meetings[:i] + remaining_meetings[i+1:]
            candidate = search(end_time, meeting["location"], new_remaining, new_schedule)
            if len(candidate) > len(best_schedule):
                best_schedule = candidate
    return best_schedule

# Format the schedule so that times are in "H:MM" format (24-hour clock)
def format_schedule(schedule):
    formatted = []
    for entry in schedule:
        formatted.append({
            "action": entry["action"],
            "location": entry["location"],
            "person": entry["person"],
            "start_time": minutes_to_time(entry["start_time"]),
            "end_time": minutes_to_time(entry["end_time"])
        })
    return formatted

# Starting conditions: you arrive at Marina District at 9:00AM.
initial_time = time_to_minutes("9:00")
initial_location = "Marina District"

best_itinerary = search(initial_time, initial_location, meetings, [])

output = {
    "itinerary": format_schedule(best_itinerary)
}

print(json.dumps(output, indent=2))