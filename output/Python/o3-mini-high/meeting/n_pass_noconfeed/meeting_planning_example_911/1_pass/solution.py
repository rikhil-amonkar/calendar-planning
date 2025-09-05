#!/usr/bin/env python3
import json

def minutes_to_time_str(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

# Travel time matrix (in minutes) as provided.
travel_times = {
    "The Castro": {
        "North Beach": 20,
        "Golden Gate Park": 11,
        "Embarcadero": 22,
        "Haight-Ashbury": 6,
        "Richmond District": 16,
        "Nob Hill": 16,
        "Marina District": 21,
        "Presidio": 20,
        "Union Square": 19,
        "Financial District": 21
    },
    "North Beach": {
        "The Castro": 23,
        "Golden Gate Park": 22,
        "Embarcadero": 6,
        "Haight-Ashbury": 18,
        "Richmond District": 18,
        "Nob Hill": 7,
        "Marina District": 9,
        "Presidio": 17,
        "Union Square": 7,
        "Financial District": 8
    },
    "Golden Gate Park": {
        "The Castro": 13,
        "North Beach": 23,
        "Embarcadero": 25,
        "Haight-Ashbury": 7,
        "Richmond District": 7,
        "Nob Hill": 20,
        "Marina District": 16,
        "Presidio": 11,
        "Union Square": 22,
        "Financial District": 26
    },
    "Embarcadero": {
        "The Castro": 25,
        "North Beach": 5,
        "Golden Gate Park": 25,
        "Haight-Ashbury": 20,
        "Richmond District": 21,
        "Nob Hill": 10,
        "Marina District": 12,
        "Presidio": 20,
        "Union Square": 10,
        "Financial District": 5
    },
    "Haight-Ashbury": {
        "The Castro": 6,
        "North Beach": 19,
        "Golden Gate Park": 7,
        "Embarcadero": 20,
        "Richmond District": 10,
        "Nob Hill": 15,
        "Marina District": 17,
        "Presidio": 15,
        "Union Square": 19,
        "Financial District": 21
    },
    "Richmond District": {
        "The Castro": 16,
        "North Beach": 17,
        "Golden Gate Park": 9,
        "Embarcadero": 19,
        "Haight-Ashbury": 10,
        "Nob Hill": 17,
        "Marina District": 9,
        "Presidio": 7,
        "Union Square": 21,
        "Financial District": 22
    },
    "Nob Hill": {
        "The Castro": 17,
        "North Beach": 8,
        "Golden Gate Park": 17,
        "Embarcadero": 9,
        "Haight-Ashbury": 13,
        "Richmond District": 14,
        "Marina District": 11,
        "Presidio": 17,
        "Union Square": 7,
        "Financial District": 9
    },
    "Marina District": {
        "The Castro": 22,
        "North Beach": 11,
        "Golden Gate Park": 18,
        "Embarcadero": 14,
        "Haight-Ashbury": 16,
        "Richmond District": 11,
        "Nob Hill": 12,
        "Presidio": 10,
        "Union Square": 16,
        "Financial District": 17
    },
    "Presidio": {
        "The Castro": 21,
        "North Beach": 18,
        "Golden Gate Park": 12,
        "Embarcadero": 20,
        "Haight-Ashbury": 15,
        "Richmond District": 7,
        "Nob Hill": 18,
        "Marina District": 11,
        "Union Square": 22,
        "Financial District": 23
    },
    "Union Square": {
        "The Castro": 17,
        "North Beach": 10,
        "Golden Gate Park": 22,
        "Embarcadero": 11,
        "Haight-Ashbury": 18,
        "Richmond District": 20,
        "Nob Hill": 9,
        "Marina District": 18,
        "Presidio": 24,
        "Financial District": 9
    },
    "Financial District": {
        "The Castro": 20,
        "North Beach": 7,
        "Golden Gate Park": 23,
        "Embarcadero": 4,
        "Haight-Ashbury": 19,
        "Richmond District": 21,
        "Nob Hill": 8,
        "Marina District": 15,
        "Presidio": 22,
        "Union Square": 9
    }
}

# Meeting constraints.
# Times are represented in minutes from midnight.
meetings = [
    {"person": "Steven", "location": "North Beach", "avail_start": 17 * 60 + 30, "avail_end": 20 * 60 + 30, "duration": 15},
    {"person": "Sarah", "location": "Golden Gate Park", "avail_start": 17 * 60, "avail_end": 19 * 60 + 15, "duration": 75},
    {"person": "Brian", "location": "Embarcadero", "avail_start": 14 * 60 + 15, "avail_end": 16 * 60, "duration": 105},
    {"person": "Stephanie", "location": "Haight-Ashbury", "avail_start": 10 * 60 + 15, "avail_end": 12 * 60 + 15, "duration": 75},
    {"person": "Melissa", "location": "Richmond District", "avail_start": 14 * 60, "avail_end": 19 * 60 + 30, "duration": 30},
    {"person": "Nancy", "location": "Nob Hill", "avail_start": 8 * 60 + 15, "avail_end": 12 * 60 + 45, "duration": 90},
    {"person": "David", "location": "Marina District", "avail_start": 11 * 60 + 15, "avail_end": 13 * 60 + 15, "duration": 120},
    {"person": "James", "location": "Presidio", "avail_start": 15 * 60, "avail_end": 18 * 60 + 15, "duration": 120},
    {"person": "Elizabeth", "location": "Union Square", "avail_start": 11 * 60 + 30, "avail_end": 21 * 60, "duration": 60},
    {"person": "Robert", "location": "Financial District", "avail_start": 13 * 60 + 15, "avail_end": 15 * 60 + 15, "duration": 45}
]

# Global best schedule (the one with the maximum number of meetings attended).
best_schedule = []

# Depth-first search to build feasible schedules.
def dfs(current_location, current_time, schedule, remaining):
    global best_schedule
    # Update best schedule if this one has more meetings.
    if len(schedule) > len(best_schedule):
        best_schedule = schedule[:]
    # Try every remaining meeting (order does not matter).
    for meeting in remaining:
        # Compute travel time from current location to the meeting location.
        travel = travel_times[current_location][meeting["location"]]
        arrival = current_time + travel
        # The meeting can only start when both you have arrived and the meeting location is available.
        start_time_meeting = max(arrival, meeting["avail_start"])
        finish_time = start_time_meeting + meeting["duration"]
        # Check if meeting can be completed within the person's available window.
        if finish_time <= meeting["avail_end"]:
            new_schedule = schedule + [{
                "person": meeting["person"],
                "location": meeting["location"],
                "start": start_time_meeting,
                "end": finish_time
            }]
            new_remaining = [m for m in remaining if m != meeting]
            dfs(meeting["location"], finish_time, new_schedule, new_remaining)

# Starting point: You arrive at The Castro at 9:00 AM.
start_location = "The Castro"
start_time = 9 * 60  # 9:00 AM in minutes

dfs(start_location, start_time, [], meetings)

# Prepare the itinerary output with properly formatted times.
itinerary = []
for event in best_schedule:
    itinerary.append({
        "action": "meet",
        "location": event["location"],
        "person": event["person"],
        "start_time": minutes_to_time_str(event["start"]),
        "end_time": minutes_to_time_str(event["end"])
    })

# Output the result as a JSON-formatted dictionary.
output = {
    "itinerary": itinerary
}
print(json.dumps(output, indent=2))