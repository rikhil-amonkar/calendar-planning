#!/usr/bin/env python3
import json
import sys
from copy import deepcopy

# Helper function: convert time from minutes since midnight to H:MM string (24hr, no leading zero for hour)
def minutes_to_time(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

# Define travel times dictionary. We'll use the given asymmetric travel times.
travel_times = {
    "Fisherman's Wharf": {
        "The Castro": 26,
        "Golden Gate Park": 25,
        "Embarcadero": 8,
        "Russian Hill": 7,
        "Nob Hill": 11,
        "Alamo Square": 20,
        "North Beach": 6
    },
    "The Castro": {
        "Fisherman's Wharf": 24,
        "Golden Gate Park": 11,
        "Embarcadero": 22,
        "Russian Hill": 18,
        "Nob Hill": 16,
        "Alamo Square": 8,
        "North Beach": 20
    },
    "Golden Gate Park": {
        "Fisherman's Wharf": 24,
        "The Castro": 13,
        "Embarcadero": 25,
        "Russian Hill": 19,
        "Nob Hill": 20,
        "Alamo Square": 10,
        "North Beach": 24
    },
    "Embarcadero": {
        "Fisherman's Wharf": 6,
        "The Castro": 25,
        "Golden Gate Park": 25,
        "Russian Hill": 8,
        "Nob Hill": 10,
        "Alamo Square": 19,
        "North Beach": 5
    },
    "Russian Hill": {
        "Fisherman's Wharf": 7,
        "The Castro": 21,
        "Golden Gate Park": 21,
        "Embarcadero": 8,
        "Nob Hill": 5,
        "Alamo Square": 15,
        "North Beach": 5
    },
    "Nob Hill": {
        "Fisherman's Wharf": 11,
        "The Castro": 17,
        "Golden Gate Park": 17,
        "Embarcadero": 9,
        "Russian Hill": 5,
        "Alamo Square": 11,
        "North Beach": 8
    },
    "Alamo Square": {
        "Fisherman's Wharf": 19,
        "The Castro": 8,
        "Golden Gate Park": 9,
        "Embarcadero": 17,
        "Russian Hill": 13,
        "Nob Hill": 11,
        "North Beach": 15
    },
    "North Beach": {
        "Fisherman's Wharf": 5,
        "The Castro": 22,
        "Golden Gate Park": 22,
        "Embarcadero": 6,
        "Russian Hill": 4,
        "Nob Hill": 7,
        "Alamo Square": 16
    }
}

# Define meeting constraints with availability windows in minutes (since midnight)
# Times are converted from HH:MM to minutes:
#   7:00  -> 420, 7:30 -> 450, 9:00 -> 540, 9:15 -> 555, 9:30 -> 570,
#   11:30 -> 690, 12:45 -> 765, 14:30 -> 870, 15:45 -> 945, 19:15 -> 1155,
#   19:30 -> 1170, 19:45 -> 1185, 7:45PM -> 19:45 (1185), 9:30PM -> 21:30 -> 1290,
#   9:15PM -> 21:15 -> 1275, 9:45 PM -> 21:45 -> 1305.
# Our starting point: Fisherman's Wharf at 9:00 (540)

meetings = [
    # person, location, avail_start, avail_end, required_duration
    # William: at Embarcadero (7:00 to 9:00, duration=90)
    {"person": "William", "location": "Embarcadero", "avail_start": 420, "avail_end": 540, "duration": 90},
    # Stephanie: at Nob Hill (7:30 to 9:30, duration=45)
    {"person": "Stephanie", "location": "Nob Hill", "avail_start": 450, "avail_end": 570, "duration": 45},
    # Joseph: at Alamo Square (11:30 to 12:45, duration=15)
    {"person": "Joseph", "location": "Alamo Square", "avail_start": 690, "avail_end": 765, "duration": 15},
    # Karen: at Russian Hill (14:30 to 19:45, duration=30)
    {"person": "Karen", "location": "Russian Hill", "avail_start": 870, "avail_end": 1185, "duration": 30},
    # Kimberly: at North Beach (15:45 to 19:15, duration=30)
    {"person": "Kimberly", "location": "North Beach", "avail_start": 945, "avail_end": 1155, "duration": 30},
    # Laura: at The Castro (19:45 to 21:30, duration=105)
    {"person": "Laura", "location": "The Castro", "avail_start": 1185, "avail_end": 1290, "duration": 105},
    # Daniel: at Golden Gate Park (21:15 to 21:45, duration=15)
    {"person": "Daniel", "location": "Golden Gate Park", "avail_start": 1275, "avail_end": 1305, "duration": 15},
]

# Our starting location and time
start_location = "Fisherman's Wharf"
start_time = 540  # 9:00

# We want to maximize number of meetings (friends met).
# We cannot meet meetings that are not possible given travel and waiting times.
# We'll use DFS to try all orderings (the number of meetings is small).

best_schedule = None
best_count = 0

def dfs(current_loc, current_time, remaining_meetings, schedule):
    global best_schedule, best_count
    # Update best_schedule if this schedule has more meetings
    if len(schedule) > best_count:
        best_count = len(schedule)
        best_schedule = deepcopy(schedule)
    # Try to add each remaining meeting that is feasible
    for i, meet in enumerate(remaining_meetings):
        # Check if travel is possible: if current_loc equals meeting location,
        # travel time is 0, otherwise get from travel_times dictionary.
        if current_loc == meet["location"]:
            travel = 0
        else:
            # if travel time not defined, skip (should not happen)
            if current_loc not in travel_times or meet["location"] not in travel_times[current_loc]:
                continue
            travel = travel_times[current_loc][meet["location"]]
        arrival_time = current_time + travel
        # The meeting can only start when the friend is available.
        meeting_start = max(arrival_time, meet["avail_start"])
        meeting_end = meeting_start + meet["duration"]
        if meeting_end <= meet["avail_end"]:
            # It's feasible, add to schedule.
            event = {
                "action": "meet",
                "location": meet["location"],
                "person": meet["person"],
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            }
            new_schedule = schedule + [event]
            new_remaining = remaining_meetings[:i] + remaining_meetings[i+1:]
            dfs(meet["location"], meeting_end, new_remaining, new_schedule)
    # End DFS

# Start DFS from starting location and time with all meetings available.
dfs(start_location, start_time, meetings, [])

# Our goal is "meet as many friends as possible". If best_schedule is None, then no meeting is feasible.
if best_schedule is None:
    result = {"itinerary": []}
else:
    result = {"itinerary": best_schedule}

# Output the result as JSON.
print(json.dumps(result, indent=2))
    
if __name__ == '__main__':
    sys.exit(0)