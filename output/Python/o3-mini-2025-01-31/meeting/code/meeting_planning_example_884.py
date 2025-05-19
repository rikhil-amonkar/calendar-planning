#!/usr/bin/env python3
import json
import copy

# Helper function: convert minutes to "H:MM" 24-hour format (no leading zero for hour)
def format_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Define travel times between locations as a nested dictionary.
travel_times = {
    "Richmond District": {
        "Chinatown": 20,
        "Sunset District": 11,
        "Alamo Square": 13,
        "Financial District": 22,
        "North Beach": 17,
        "Embarcadero": 19,
        "Presidio": 7,
        "Golden Gate Park": 9,
        "Bayview": 27
    },
    "Chinatown": {
        "Richmond District": 20,
        "Sunset District": 29,
        "Alamo Square": 17,
        "Financial District": 5,
        "North Beach": 3,
        "Embarcadero": 5,
        "Presidio": 19,
        "Golden Gate Park": 23,
        "Bayview": 20
    },
    "Sunset District": {
        "Richmond District": 12,
        "Chinatown": 30,
        "Alamo Square": 16,
        "Financial District": 30,
        "North Beach": 28,
        "Embarcadero": 30,
        "Presidio": 16,
        "Golden Gate Park": 11,
        "Bayview": 22
    },
    "Alamo Square": {
        "Richmond District": 11,
        "Chinatown": 15,
        "Sunset District": 16,
        "Financial District": 17,
        "North Beach": 15,
        "Embarcadero": 16,
        "Presidio": 17,
        "Golden Gate Park": 9,
        "Bayview": 16
    },
    "Financial District": {
        "Richmond District": 21,
        "Chinatown": 5,
        "Sunset District": 30,
        "Alamo Square": 17,
        "North Beach": 7,
        "Embarcadero": 4,
        "Presidio": 22,
        "Golden Gate Park": 23,
        "Bayview": 19
    },
    "North Beach": {
        "Richmond District": 18,
        "Chinatown": 6,
        "Sunset District": 27,
        "Alamo Square": 16,
        "Financial District": 8,
        "Embarcadero": 6,
        "Presidio": 17,
        "Golden Gate Park": 22,
        "Bayview": 25
    },
    "Embarcadero": {
        "Richmond District": 21,
        "Chinatown": 7,
        "Sunset District": 30,
        "Alamo Square": 19,
        "Financial District": 5,
        "North Beach": 5,
        "Presidio": 20,
        "Golden Gate Park": 25,
        "Bayview": 21
    },
    "Presidio": {
        "Richmond District": 7,
        "Chinatown": 21,
        "Sunset District": 15,
        "Alamo Square": 19,
        "Financial District": 23,
        "North Beach": 18,
        "Embarcadero": 20,
        "Golden Gate Park": 12,
        "Bayview": 31
    },
    "Golden Gate Park": {
        "Richmond District": 7,
        "Chinatown": 23,
        "Sunset District": 10,
        "Alamo Square": 9,
        "Financial District": 26,
        "North Beach": 23,
        "Embarcadero": 25,
        "Presidio": 11,
        "Bayview": 23
    },
    "Bayview": {
        "Richmond District": 25,
        "Chinatown": 19,
        "Sunset District": 23,
        "Alamo Square": 16,
        "Financial District": 19,
        "North Beach": 22,
        "Embarcadero": 19,
        "Presidio": 32,
        "Golden Gate Park": 22
    }
}

# Define meeting constraints.
# Times are in minutes from midnight.
meetings = {
    "Robert": {
        "location": "Chinatown",
        "avail_start": 7 * 60 + 45,   # 7:45 -> 465
        "avail_end": 17 * 60 + 30,      # 17:30 -> 1050
        "duration": 120
    },
    "David": {
        "location": "Sunset District",
        "avail_start": 12 * 60 + 30,    # 12:30 -> 750
        "avail_end": 19 * 60 + 45,      # 19:45 -> 1185
        "duration": 45
    },
    "Matthew": {
        "location": "Alamo Square",
        "avail_start": 8 * 60 + 45,     # 8:45 -> 525
        "avail_end": 13 * 60 + 45,      # 13:45 -> 825
        "duration": 90
    },
    "Jessica": {
        "location": "Financial District",
        "avail_start": 9 * 60 + 30,     # 9:30 -> 570
        "avail_end": 18 * 60 + 45,      # 18:45 -> 1125
        "duration": 45
    },
    "Melissa": {
        "location": "North Beach",
        "avail_start": 7 * 60 + 15,     # 7:15 -> 435
        "avail_end": 16 * 60 + 45,      # 16:45 -> 1005
        "duration": 45
    },
    "Mark": {
        "location": "Embarcadero",
        "avail_start": 15 * 60 + 15,    # 15:15 -> 915
        "avail_end": 17 * 60 + 0,       # 17:00 -> 1020
        "duration": 45
    },
    "Deborah": {
        "location": "Presidio",
        "avail_start": 19 * 60 + 0,     # 19:00 -> 1140
        "avail_end": 19 * 60 + 45,      # 19:45 -> 1185
        "duration": 45
    },
    "Karen": {
        "location": "Golden Gate Park",
        "avail_start": 19 * 60 + 30,    # 19:30 -> 1170
        "avail_end": 22 * 60 + 0,       # 22:00 -> 1320
        "duration": 120
    },
    "Laura": {
        "location": "Bayview",
        "avail_start": 21 * 60 + 15,    # 21:15 -> 1275
        "avail_end": 22 * 60 + 15,      # 22:15 -> 1335
        "duration": 15
    }
}

# Starting point
start_location = "Richmond District"
start_time = 9 * 60   # 9:00 -> 540 minutes

# Global best schedule (maximizing count of meetings)
best_schedule = []
best_count = 0

# Recursive DFS search through meeting orders.
def search(current_loc, current_time, remaining, schedule):
    global best_schedule, best_count
    # Update best if current schedule is longer.
    if len(schedule) > best_count:
        best_schedule = copy.deepcopy(schedule)
        best_count = len(schedule)
    # Try each meeting in remaining
    for person, details in list(remaining.items()):
        meeting_location = details["location"]
        # Get travel time
        travel = travel_times[current_loc][meeting_location]
        arrival_time = current_time + travel
        # Determine meeting start time: maximum of arrival time and person's start window.
        meeting_start = max(arrival_time, details["avail_start"])
        meeting_end = meeting_start + details["duration"]
        # Check if meeting can finish before person's availability ends.
        if meeting_end <= details["avail_end"]:
            # Create a meeting entry.
            meeting_entry = {
                "action": "meet",
                "location": meeting_location,
                "person": person,
                "start_time": format_time(meeting_start),
                "end_time": format_time(meeting_end)
            }
            # Prepare new remaining dictionary without this meeting.
            new_remaining = remaining.copy()
            del new_remaining[person]
            # Continue search from this meeting's end time and location.
            new_schedule = schedule + [meeting_entry]
            search(meeting_location, meeting_end, new_remaining, new_schedule)

# Start search from the starting point.
search(start_location, start_time, meetings, [])

# Prepare result JSON:
result = {
    "itinerary": best_schedule
}

print(json.dumps(result, indent=2))