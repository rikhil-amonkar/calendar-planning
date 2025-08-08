#!/usr/bin/env python3
import json

def minutes_to_time_str(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Define travel times (in minutes) between locations.
travel_times = {
    "Embarcadero": {
        "Bayview": 21,
        "Chinatown": 7,
        "Alamo Square": 19,
        "Nob Hill": 10,
        "Presidio": 20,
        "Union Square": 10,
        "The Castro": 25,
        "North Beach": 5,
        "Fisherman's Wharf": 6,
        "Marina District": 12
    },
    "Bayview": {
        "Embarcadero": 19,
        "Chinatown": 19,
        "Alamo Square": 16,
        "Nob Hill": 20,
        "Presidio": 32,
        "Union Square": 18,
        "The Castro": 19,
        "North Beach": 22,
        "Fisherman's Wharf": 25,
        "Marina District": 27
    },
    "Chinatown": {
        "Embarcadero": 5,
        "Bayview": 20,
        "Alamo Square": 17,
        "Nob Hill": 9,
        "Presidio": 19,
        "Union Square": 7,
        "The Castro": 22,
        "North Beach": 3,
        "Fisherman's Wharf": 8,
        "Marina District": 12
    },
    "Alamo Square": {
        "Embarcadero": 16,
        "Bayview": 16,
        "Chinatown": 15,
        "Nob Hill": 11,
        "Presidio": 17,
        "Union Square": 14,
        "The Castro": 8,
        "North Beach": 15,
        "Fisherman's Wharf": 19,
        "Marina District": 15
    },
    "Nob Hill": {
        "Embarcadero": 9,
        "Bayview": 19,
        "Chinatown": 6,
        "Alamo Square": 11,
        "Presidio": 17,
        "Union Square": 7,
        "The Castro": 17,
        "North Beach": 8,
        "Fisherman's Wharf": 10,
        "Marina District": 11
    },
    "Presidio": {
        "Embarcadero": 20,
        "Bayview": 31,
        "Chinatown": 21,
        "Alamo Square": 19,
        "Nob Hill": 18,
        "Union Square": 22,
        "The Castro": 21,
        "North Beach": 18,
        "Fisherman's Wharf": 19,
        "Marina District": 11
    },
    "Union Square": {
        "Embarcadero": 11,
        "Bayview": 15,
        "Chinatown": 7,
        "Alamo Square": 15,
        "Nob Hill": 9,
        "Presidio": 24,
        "The Castro": 17,
        "North Beach": 10,
        "Fisherman's Wharf": 15,
        "Marina District": 18
    },
    "The Castro": {
        "Embarcadero": 22,
        "Bayview": 19,
        "Chinatown": 22,
        "Alamo Square": 8,
        "Nob Hill": 16,
        "Presidio": 20,
        "Union Square": 19,
        "North Beach": 20,
        "Fisherman's Wharf": 24,
        "Marina District": 21
    },
    "North Beach": {
        "Embarcadero": 6,
        "Bayview": 25,
        "Chinatown": 6,
        "Alamo Square": 16,
        "Nob Hill": 7,
        "Presidio": 17,
        "Union Square": 7,
        "The Castro": 23,
        "Fisherman's Wharf": 5,
        "Marina District": 9
    },
    "Fisherman's Wharf": {
        "Embarcadero": 8,
        "Bayview": 26,
        "Chinatown": 12,
        "Alamo Square": 21,
        "Nob Hill": 11,
        "Presidio": 17,
        "Union Square": 13,
        "The Castro": 27,
        "North Beach": 6,
        "Marina District": 9
    },
    "Marina District": {
        "Embarcadero": 14,
        "Bayview": 27,
        "Chinatown": 15,
        "Alamo Square": 15,
        "Nob Hill": 12,
        "Presidio": 10,
        "Union Square": 16,
        "The Castro": 22,
        "North Beach": 11,
        "Fisherman's Wharf": 10
    }
}

# Meeting constraints.
# Times are represented in minutes from midnight.
# Arrival at Embarcadero is 9:00 AM which is 540 minutes.
# Friends' availabilities (converted to 24-hour minutes) and required meeting durations:
meetings = [
    {"person": "Matthew", "location": "Bayview", "avail_start": 1155, "avail_end": 1320, "duration": 120},   # 19:15-22:00
    {"person": "Karen",   "location": "Chinatown", "avail_start": 1155, "avail_end": 1275, "duration": 90},   # 19:15-21:15
    {"person": "Sarah",   "location": "Alamo Square", "avail_start": 1200, "avail_end": 1305, "duration": 105}, # 20:00-21:45
    {"person": "Jessica", "location": "Nob Hill", "avail_start": 990, "avail_end": 1125, "duration": 120},      # 16:30-18:45
    {"person": "Stephanie", "location": "Presidio", "avail_start": 450, "avail_end": 615, "duration": 60},      # 7:30-10:15
    {"person": "Mary",    "location": "Union Square", "avail_start": 1005, "avail_end": 1290, "duration": 60},  # 16:45-21:30
    {"person": "Charles", "location": "The Castro", "avail_start": 990, "avail_end": 1320, "duration": 105},     # 16:30-22:00
    {"person": "Nancy",   "location": "North Beach", "avail_start": 885, "avail_end": 1200, "duration": 15},     # 14:45-20:00
    {"person": "Thomas",  "location": "Fisherman's Wharf", "avail_start": 810, "avail_end": 1140, "duration": 30}, # 13:30-19:00
    {"person": "Brian",   "location": "Marina District", "avail_start": 735, "avail_end": 1080, "duration": 60}   # 12:15-18:00
]

# Sort meetings by their availability start time to help guide the search.
meetings.sort(key=lambda m: m["avail_start"])

# Global variable for the best schedule (maximizing number of meetings)
best_schedule = []

def dfs(current_location, current_time, scheduled, remaining):
    global best_schedule
    # If we have scheduled more meetings than our current best, update the best.
    if len(scheduled) > len(best_schedule):
        best_schedule = scheduled[:]
    # Try each remaining meeting and see if it can be scheduled next.
    for i, meeting in enumerate(remaining):
        # Compute travel time from current location to meeting location.
        travel_time = travel_times[current_location][meeting["location"]]
        arrival_time = current_time + travel_time
        # The meeting cannot start before the friend’s available start.
        meeting_start = max(arrival_time, meeting["avail_start"])
        meeting_end = meeting_start + meeting["duration"]
        # Check if the meeting can be completed before the friend’s availability ends.
        if meeting_end <= meeting["avail_end"]:
            new_scheduled = scheduled + [{
                "person": meeting["person"],
                "location": meeting["location"],
                "start": meeting_start,
                "end": meeting_end
            }]
            new_remaining = remaining[:i] + remaining[i+1:]
            dfs(meeting["location"], meeting_end, new_scheduled, new_remaining)

# Start DFS from the Embarcadero at 9:00 (540 minutes)
dfs("Embarcadero", 540, [], meetings)

# Convert the best schedule times from minutes to formatted strings.
itinerary = []
for event in best_schedule:
    itinerary.append({
        "action": "meet",
        "location": event["location"],
        "person": event["person"],
        "start_time": minutes_to_time_str(event["start"]),
        "end_time": minutes_to_time_str(event["end"])
    })

result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))