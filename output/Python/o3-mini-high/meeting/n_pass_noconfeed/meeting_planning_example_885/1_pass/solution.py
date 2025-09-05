#!/usr/bin/env python3
import json

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times (in minutes) between locations.
travel = {
    "Russian Hill": {
        "Marina District": 7,
        "Financial District": 11,
        "Alamo Square": 15,
        "Golden Gate Park": 21,
        "The Castro": 21,
        "Bayview": 23,
        "Sunset District": 23,
        "Haight-Ashbury": 17,
        "Nob Hill": 5
    },
    "Marina District": {
        "Russian Hill": 8,
        "Financial District": 17,
        "Alamo Square": 15,
        "Golden Gate Park": 18,
        "The Castro": 22,
        "Bayview": 27,
        "Sunset District": 19,
        "Haight-Ashbury": 16,
        "Nob Hill": 12
    },
    "Financial District": {
        "Russian Hill": 11,
        "Marina District": 15,
        "Alamo Square": 17,
        "Golden Gate Park": 23,
        "The Castro": 20,
        "Bayview": 19,
        "Sunset District": 30,
        "Haight-Ashbury": 19,
        "Nob Hill": 8
    },
    "Alamo Square": {
        "Russian Hill": 13,
        "Marina District": 15,
        "Financial District": 17,
        "Golden Gate Park": 9,
        "The Castro": 8,
        "Bayview": 16,
        "Sunset District": 16,
        "Haight-Ashbury": 5,
        "Nob Hill": 11
    },
    "Golden Gate Park": {
        "Russian Hill": 19,
        "Marina District": 16,
        "Financial District": 26,
        "Alamo Square": 9,
        "The Castro": 13,
        "Bayview": 23,
        "Sunset District": 10,
        "Haight-Ashbury": 7,
        "Nob Hill": 20
    },
    "The Castro": {
        "Russian Hill": 18,
        "Marina District": 21,
        "Financial District": 21,
        "Alamo Square": 8,
        "Golden Gate Park": 11,
        "Bayview": 19,
        "Sunset District": 17,
        "Haight-Ashbury": 6,
        "Nob Hill": 16
    },
    "Bayview": {
        "Russian Hill": 23,
        "Marina District": 27,
        "Financial District": 19,
        "Alamo Square": 16,
        "Golden Gate Park": 22,
        "The Castro": 19,
        "Sunset District": 23,
        "Haight-Ashbury": 19,
        "Nob Hill": 20
    },
    "Sunset District": {
        "Russian Hill": 24,
        "Marina District": 21,
        "Financial District": 30,
        "Alamo Square": 17,
        "Golden Gate Park": 11,
        "The Castro": 17,
        "Bayview": 22,
        "Haight-Ashbury": 15,
        "Nob Hill": 27
    },
    "Haight-Ashbury": {
        "Russian Hill": 17,
        "Marina District": 17,
        "Financial District": 21,
        "Alamo Square": 5,
        "Golden Gate Park": 7,
        "The Castro": 6,
        "Bayview": 18,
        "Sunset District": 15,
        "Nob Hill": 15
    },
    "Nob Hill": {
        "Russian Hill": 5,
        "Marina District": 11,
        "Financial District": 9,
        "Alamo Square": 11,
        "Golden Gate Park": 17,
        "The Castro": 17,
        "Bayview": 19,
        "Sunset District": 24,
        "Haight-Ashbury": 13
    }
}

# Meeting constraints.
# Each friend is represented with a dictionary containing:
# - person: Name
# - location: Meeting location
# - avail_start, avail_end: availability window (in minutes from midnight)
# - duration: required meeting duration (in minutes)
meetings = [
    {
        "person": "Mark",
        "location": "Marina District",
        "avail_start": 18 * 60 + 45,  # 18:45
        "avail_end": 21 * 60,         # 21:00
        "duration": 90
    },
    {
        "person": "Karen",
        "location": "Financial District",
        "avail_start": 9 * 60 + 30,   # 9:30
        "avail_end": 12 * 60 + 45,      # 12:45
        "duration": 90
    },
    {
        "person": "Barbara",
        "location": "Alamo Square",
        "avail_start": 10 * 60,       # 10:00
        "avail_end": 19 * 60 + 30,      # 19:30
        "duration": 90
    },
    {
        "person": "Nancy",
        "location": "Golden Gate Park",
        "avail_start": 16 * 60 + 45,  # 16:45
        "avail_end": 20 * 60,         # 20:00
        "duration": 105
    },
    {
        "person": "David",
        "location": "The Castro",
        "avail_start": 9 * 60,        # 9:00
        "avail_end": 18 * 60,         # 18:00
        "duration": 120
    },
    {
        "person": "Linda",
        "location": "Bayview",
        "avail_start": 18 * 60 + 15,  # 18:15
        "avail_end": 19 * 60 + 45,     # 19:45
        "duration": 45
    },
    {
        "person": "Kevin",
        "location": "Sunset District",
        "avail_start": 10 * 60,       # 10:00
        "avail_end": 17 * 60 + 45,      # 17:45
        "duration": 120
    },
    {
        "person": "Matthew",
        "location": "Haight-Ashbury",
        "avail_start": 10 * 60 + 15,  # 10:15
        "avail_end": 15 * 60 + 30,     # 15:30
        "duration": 45
    },
    {
        "person": "Andrew",
        "location": "Nob Hill",
        "avail_start": 11 * 60 + 45,  # 11:45
        "avail_end": 16 * 60 + 45,     # 16:45
        "duration": 105
    }
]

# Our starting point: arriving at Russian Hill at 9:00.
start_time = 9 * 60  # 9:00 in minutes from midnight
start_location = "Russian Hill"

best_schedule = []
best_count = 0

# Depth-first search to explore possible meeting orders.
def dfs(current_time, current_location, remaining, current_schedule):
    global best_schedule, best_count

    # Update best schedule if current one has more meetings.
    if len(current_schedule) > best_count:
        best_count = len(current_schedule)
        best_schedule = current_schedule[:]
    
    # Try to schedule each remaining meeting.
    for i, meeting in enumerate(remaining):
        # Calculate arrival time at the meeting location.
        travel_time = travel[current_location][meeting["location"]]
        arrival_time = current_time + travel_time
        # The meeting can only start after arrival and not before the friend's available start time.
        meeting_start = max(arrival_time, meeting["avail_start"])
        meeting_end = meeting_start + meeting["duration"]
        # Check if the meeting can finish within the friend's available window.
        if meeting_end <= meeting["avail_end"]:
            new_schedule = current_schedule[:]            
            new_schedule.append({
                "action": "meet",
                "location": meeting["location"],
                "person": meeting["person"],
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            })
            new_remaining = remaining[:i] + remaining[i+1:]
            dfs(meeting_end, meeting["location"], new_remaining, new_schedule)

# Start the DFS search from the starting point.
dfs(start_time, start_location, meetings, [])

# Prepare the result as a JSON structure.
result = {"itinerary": best_schedule}
print(json.dumps(result))