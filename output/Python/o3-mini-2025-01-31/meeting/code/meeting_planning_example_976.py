#!/usr/bin/env python3
import json
from copy import deepcopy

# Helper functions for time conversions
def time_to_minutes(t):
    # t is a string in "H:MM" 24-hour format (e.g., "9:00", "13:30")
    parts = t.split(":")
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(m):
    # Convert minutes to "H:MM" format (24-hour, no leading zero for hours)
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Define travel times as a nested dictionary (all times in minutes)
travel_times = {
    "Embarcadero": {
        "Bayview": 21, "Chinatown": 7, "Alamo Square": 19, "Nob Hill": 10,
        "Presidio": 20, "Union Square": 10, "The Castro": 25, "North Beach": 5,
        "Fisherman's Wharf": 6, "Marina District": 12
    },
    "Bayview": {
        "Embarcadero": 19, "Chinatown": 19, "Alamo Square": 16, "Nob Hill": 20,
        "Presidio": 32, "Union Square": 18, "The Castro": 19, "North Beach": 22,
        "Fisherman's Wharf": 25, "Marina District": 27
    },
    "Chinatown": {
        "Embarcadero": 5, "Bayview": 20, "Alamo Square": 17, "Nob Hill": 9,
        "Presidio": 19, "Union Square": 7, "The Castro": 22, "North Beach": 3,
        "Fisherman's Wharf": 8, "Marina District": 12
    },
    "Alamo Square": {
        "Embarcadero": 16, "Bayview": 16, "Chinatown": 15, "Nob Hill": 11,
        "Presidio": 17, "Union Square": 14, "The Castro": 8, "North Beach": 15,
        "Fisherman's Wharf": 19, "Marina District": 15
    },
    "Nob Hill": {
        "Embarcadero": 9, "Bayview": 19, "Chinatown": 6, "Alamo Square": 11,
        "Presidio": 17, "Union Square": 7, "The Castro": 17, "North Beach": 8,
        "Fisherman's Wharf": 10, "Marina District": 11
    },
    "Presidio": {
        "Embarcadero": 20, "Bayview": 31, "Chinatown": 21, "Alamo Square": 19,
        "Nob Hill": 18, "Union Square": 22, "The Castro": 21, "North Beach": 18,
        "Fisherman's Wharf": 19, "Marina District": 11
    },
    "Union Square": {
        "Embarcadero": 11, "Bayview": 15, "Chinatown": 7, "Alamo Square": 15,
        "Nob Hill": 9, "Presidio": 24, "The Castro": 17, "North Beach": 10,
        "Fisherman's Wharf": 15, "Marina District": 18
    },
    "The Castro": {
        "Embarcadero": 22, "Bayview": 19, "Chinatown": 22, "Alamo Square": 8,
        "Nob Hill": 16, "Presidio": 20, "Union Square": 19, "North Beach": 20,
        "Fisherman's Wharf": 24, "Marina District": 21
    },
    "North Beach": {
        "Embarcadero": 6, "Bayview": 25, "Chinatown": 6, "Alamo Square": 16,
        "Nob Hill": 7, "Presidio": 17, "Union Square": 7, "The Castro": 23,
        "Fisherman's Wharf": 5, "Marina District": 9
    },
    "Fisherman's Wharf": {
        "Embarcadero": 8, "Bayview": 26, "Chinatown": 12, "Alamo Square": 21,
        "Nob Hill": 11, "Presidio": 17, "Union Square": 13, "The Castro": 27,
        "North Beach": 6, "Marina District": 9
    },
    "Marina District": {
        "Embarcadero": 14, "Bayview": 27, "Chinatown": 15, "Alamo Square": 15,
        "Nob Hill": 12, "Presidio": 10, "Union Square": 16, "The Castro": 22,
        "North Beach": 11, "Fisherman's Wharf": 10
    }
}

# Define meeting appointments as list of dictionaries.
# Each appointment has: person, location, window_start, window_end, min_duration.
# Times are stored in minutes from midnight.
appointments = [
    {"person": "Matthew", "location": "Bayview", "window_start": time_to_minutes("19:15"), "window_end": time_to_minutes("22:00"), "duration": 120},
    {"person": "Karen", "location": "Chinatown", "window_start": time_to_minutes("19:15"), "window_end": time_to_minutes("21:15"), "duration": 90},
    {"person": "Sarah", "location": "Alamo Square", "window_start": time_to_minutes("20:00"), "window_end": time_to_minutes("21:45"), "duration": 105},
    {"person": "Jessica", "location": "Nob Hill", "window_start": time_to_minutes("16:30"), "window_end": time_to_minutes("18:45"), "duration": 120},
    {"person": "Stephanie", "location": "Presidio", "window_start": time_to_minutes("7:30"),  "window_end": time_to_minutes("10:15"), "duration": 60},
    {"person": "Mary", "location": "Union Square", "window_start": time_to_minutes("16:45"), "window_end": time_to_minutes("21:30"), "duration": 60},
    {"person": "Charles", "location": "The Castro", "window_start": time_to_minutes("16:30"), "window_end": time_to_minutes("22:00"), "duration": 105},
    {"person": "Nancy", "location": "North Beach", "window_start": time_to_minutes("14:45"), "window_end": time_to_minutes("20:00"), "duration": 15},
    {"person": "Thomas", "location": "Fisherman's Wharf", "window_start": time_to_minutes("13:30"), "window_end": time_to_minutes("19:00"), "duration": 30},
    {"person": "Brian", "location": "Marina District", "window_start": time_to_minutes("12:15"), "window_end": time_to_minutes("18:00"), "duration": 60},
]

# Starting point and time (Embarcadero at 9:00)
start_location = "Embarcadero"
start_time = time_to_minutes("9:00")

# Backtracking search for the optimal schedule (maximizing the count of appointments)
best_schedule = []
best_count = 0

def backtrack(current_location, current_time, remaining_appts, current_schedule):
    global best_schedule, best_count
    found = False
    # Try each remaining appointment in turn
    for i, appt in enumerate(remaining_appts):
        # Get travel time from current location to appointment location
        if current_location == appt["location"]:
            travel = 0
        else:
            travel = travel_times[current_location][appt["location"]]
        arrival_time = current_time + travel
        # The meeting can only start when the appointment is available
        meeting_start = max(arrival_time, appt["window_start"])
        meeting_end = meeting_start + appt["duration"]
        # Check if meeting can be completed within the appointment's window
        if meeting_end <= appt["window_end"]:
            # It's feasible, add to schedule
            new_schedule_item = {
                "action": "meet",
                "location": appt["location"],
                "person": appt["person"],
                "start_time": meeting_start,
                "end_time": meeting_end
            }
            new_schedule = current_schedule + [new_schedule_item]
            # Prepare remaining appointments for recursion
            new_remaining = remaining_appts[:i] + remaining_appts[i+1:]
            backtrack(appt["location"], meeting_end, new_remaining, new_schedule)
            found = True
    # If no further appointment can be scheduled, update best_schedule if count is higher
    if not found:
        if len(current_schedule) > best_count:
            best_count = len(current_schedule)
            best_schedule = current_schedule

# Start backtracking from the starting point/time
backtrack(start_location, start_time, appointments, [])

# Convert schedule times back to "H:MM" format in output itinerary
itinerary = []
for item in best_schedule:
    itinerary.append({
        "action": item["action"],
        "location": item["location"],
        "person": item["person"],
        "start_time": minutes_to_time(item["start_time"]),
        "end_time": minutes_to_time(item["end_time"])
    })

# Prepare output dictionary
output = {"itinerary": itinerary}

# Output the result as JSON
print(json.dumps(output, indent=2))