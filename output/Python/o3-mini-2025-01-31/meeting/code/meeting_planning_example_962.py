import json
from copy import deepcopy

# Utility functions to convert time formats
def to_minutes(time_str):
    # time_str in "H:MM" 24-hour format (no leading zero guaranteed)
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def to_timestr(minutes):
    # Convert minutes (int) to "H:MM" (no leading zero for hour)
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Define travel times as a dictionary of dictionaries.
travel_times = {
    "The Castro": {
        "Marina District": 21, "Presidio": 20, "North Beach": 20, "Embarcadero": 22,
        "Haight-Ashbury": 6, "Golden Gate Park": 11, "Richmond District": 16,
        "Alamo Square": 8, "Financial District": 21, "Sunset District": 17
    },
    "Marina District": {
        "The Castro": 22, "Presidio": 10, "North Beach": 11, "Embarcadero": 14,
        "Haight-Ashbury": 16, "Golden Gate Park": 18, "Richmond District": 11,
        "Alamo Square": 15, "Financial District": 17, "Sunset District": 19
    },
    "Presidio": {
        "The Castro": 21, "Marina District": 11, "North Beach": 18, "Embarcadero": 20,
        "Haight-Ashbury": 15, "Golden Gate Park": 12, "Richmond District": 7,
        "Alamo Square": 19, "Financial District": 23, "Sunset District": 15
    },
    "North Beach": {
        "The Castro": 23, "Marina District": 9, "Presidio": 17, "Embarcadero": 6,
        "Haight-Ashbury": 18, "Golden Gate Park": 22, "Richmond District": 18,
        "Alamo Square": 16, "Financial District": 8, "Sunset District": 27
    },
    "Embarcadero": {
        "The Castro": 25, "Marina District": 12, "Presidio": 20, "North Beach": 5,
        "Haight-Ashbury": 21, "Golden Gate Park": 25, "Richmond District": 21,
        "Alamo Square": 19, "Financial District": 5, "Sunset District": 30
    },
    "Haight-Ashbury": {
        "The Castro": 6, "Marina District": 17, "Presidio": 15, "North Beach": 19,
        "Embarcadero": 20, "Golden Gate Park": 7, "Richmond District": 10,
        "Alamo Square": 5, "Financial District": 21, "Sunset District": 15
    },
    "Golden Gate Park": {
        "The Castro": 13, "Marina District": 16, "Presidio": 11, "North Beach": 23,
        "Embarcadero": 25, "Haight-Ashbury": 7, "Richmond District": 7,
        "Alamo Square": 9, "Financial District": 26, "Sunset District": 10
    },
    "Richmond District": {
        "The Castro": 16, "Marina District": 9, "Presidio": 7, "North Beach": 17,
        "Embarcadero": 19, "Haight-Ashbury": 10, "Golden Gate Park": 9,
        "Alamo Square": 13, "Financial District": 22, "Sunset District": 11
    },
    "Alamo Square": {
        "The Castro": 8, "Marina District": 15, "Presidio": 17, "North Beach": 15,
        "Embarcadero": 16, "Haight-Ashbury": 5, "Golden Gate Park": 9,
        "Richmond District": 11, "Financial District": 17, "Sunset District": 16
    },
    "Financial District": {
        "The Castro": 20, "Marina District": 15, "Presidio": 22, "North Beach": 7,
        "Embarcadero": 4, "Haight-Ashbury": 19, "Golden Gate Park": 23,
        "Richmond District": 21, "Alamo Square": 17, "Sunset District": 30
    },
    "Sunset District": {
        "The Castro": 17, "Marina District": 21, "Presidio": 16, "North Beach": 28,
        "Embarcadero": 30, "Haight-Ashbury": 15, "Golden Gate Park": 11,
        "Richmond District": 12, "Alamo Square": 17, "Financial District": 30
    }
}

# Define the meeting constraints as a list of dictionaries
meetings = [
    {"person": "Elizabeth", "location": "Marina District",
     "avail_start": to_minutes("19:00"), "avail_end": to_minutes("20:45"), "duration":105},
    {"person": "Joshua", "location": "Presidio",
     "avail_start": to_minutes("8:30"), "avail_end": to_minutes("13:15"), "duration":105},
    {"person": "Timothy", "location": "North Beach",
     "avail_start": to_minutes("19:45"), "avail_end": to_minutes("22:00"), "duration":90},
    {"person": "David", "location": "Embarcadero",
     "avail_start": to_minutes("10:45"), "avail_end": to_minutes("12:30"), "duration":30},
    {"person": "Kimberly", "location": "Haight-Ashbury",
     "avail_start": to_minutes("16:45"), "avail_end": to_minutes("21:30"), "duration":75},
    {"person": "Lisa", "location": "Golden Gate Park",
     "avail_start": to_minutes("17:30"), "avail_end": to_minutes("21:45"), "duration":45},
    {"person": "Ronald", "location": "Richmond District",
     "avail_start": to_minutes("8:00"), "avail_end": to_minutes("9:30"), "duration":90},
    {"person": "Stephanie", "location": "Alamo Square",
     "avail_start": to_minutes("15:30"), "avail_end": to_minutes("16:30"), "duration":30},
    {"person": "Helen", "location": "Financial District",
     "avail_start": to_minutes("17:30"), "avail_end": to_minutes("18:30"), "duration":45},
    {"person": "Laura", "location": "Sunset District",
     "avail_start": to_minutes("17:45"), "avail_end": to_minutes("21:15"), "duration":90}
]

# Starting point: you arrive at The Castro at 9:00AM.
start_time = to_minutes("9:00")
start_location = "The Castro"

# We'll use DFS to find the schedule that meets the most meetings.
def dfs(current_time, current_location, remaining, schedule):
    best_schedule = deepcopy(schedule)
    
    # Try each meeting in remaining that is feasible next.
    for i, m in enumerate(remaining):
        # Compute travel time from current location to meeting location.
        if current_location not in travel_times or m["location"] not in travel_times[current_location]:
            continue
        travel = travel_times[current_location][m["location"]]
        arrival_time = current_time + travel
        # The meeting can only start when both you arrive and the meeting is available.
        meeting_start = max(arrival_time, m["avail_start"])
        meeting_end = meeting_start + m["duration"]
        # Check if meeting can be held within the available window.
        if meeting_end <= m["avail_end"]:
            # Create an event record to add.
            event = {
                "action": "meet",
                "location": m["location"],
                "person": m["person"],
                "start_time": to_timestr(meeting_start),
                "end_time": to_timestr(meeting_end)
            }
            new_schedule = deepcopy(schedule)
            new_schedule.append(event)
            new_remaining = remaining[:i] + remaining[i+1:]
            candidate = dfs(meeting_end, m["location"], new_remaining, new_schedule)
            # Choose the candidate schedule with more meetings.
            if len(candidate) > len(best_schedule):
                best_schedule = candidate
    return best_schedule

# Run DFS to compute the optimal schedule.
optimal_schedule = dfs(start_time, start_location, meetings, [])

# For the purposes of this problem, we want to output the itinerary.
output = {
    "itinerary": optimal_schedule
}

print(json.dumps(output, indent=2))