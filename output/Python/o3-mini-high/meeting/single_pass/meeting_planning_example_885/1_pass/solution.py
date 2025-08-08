#!/usr/bin/env python3
import json

# Helper functions to convert between time string and minutes
def parse_time(t):
    # t is in format "H:MM" (24-hour) e.g., "9:30" or "18:45"
    parts = t.split(":")
    return int(parts[0]) * 60 + int(parts[1])

def format_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times (in minutes) provided as a dictionary with (origin, destination) keys.
travel = {
  ("Russian Hill", "Marina District"): 7,
  ("Russian Hill", "Financial District"): 11,
  ("Russian Hill", "Alamo Square"): 15,
  ("Russian Hill", "Golden Gate Park"): 21,
  ("Russian Hill", "The Castro"): 21,
  ("Russian Hill", "Bayview"): 23,
  ("Russian Hill", "Sunset District"): 23,
  ("Russian Hill", "Haight-Ashbury"): 17,
  ("Russian Hill", "Nob Hill"): 5,
  
  ("Marina District", "Russian Hill"): 8,
  ("Marina District", "Financial District"): 17,
  ("Marina District", "Alamo Square"): 15,
  ("Marina District", "Golden Gate Park"): 18,
  ("Marina District", "The Castro"): 22,
  ("Marina District", "Bayview"): 27,
  ("Marina District", "Sunset District"): 19,
  ("Marina District", "Haight-Ashbury"): 16,
  ("Marina District", "Nob Hill"): 12,
  
  ("Financial District", "Russian Hill"): 11,
  ("Financial District", "Marina District"): 15,
  ("Financial District", "Alamo Square"): 17,
  ("Financial District", "Golden Gate Park"): 23,
  ("Financial District", "The Castro"): 20,
  ("Financial District", "Bayview"): 19,
  ("Financial District", "Sunset District"): 30,
  ("Financial District", "Haight-Ashbury"): 19,
  ("Financial District", "Nob Hill"): 8,
  
  ("Alamo Square", "Russian Hill"): 13,
  ("Alamo Square", "Marina District"): 15,
  ("Alamo Square", "Financial District"): 17,
  ("Alamo Square", "Golden Gate Park"): 9,
  ("Alamo Square", "The Castro"): 8,
  ("Alamo Square", "Bayview"): 16,
  ("Alamo Square", "Sunset District"): 16,
  ("Alamo Square", "Haight-Ashbury"): 5,
  ("Alamo Square", "Nob Hill"): 11,
  
  ("Golden Gate Park", "Russian Hill"): 19,
  ("Golden Gate Park", "Marina District"): 16,
  ("Golden Gate Park", "Financial District"): 26,
  ("Golden Gate Park", "Alamo Square"): 9,
  ("Golden Gate Park", "The Castro"): 13,
  ("Golden Gate Park", "Bayview"): 23,
  ("Golden Gate Park", "Sunset District"): 10,
  ("Golden Gate Park", "Haight-Ashbury"): 7,
  ("Golden Gate Park", "Nob Hill"): 20,
  
  ("The Castro", "Russian Hill"): 18,
  ("The Castro", "Marina District"): 21,
  ("The Castro", "Financial District"): 21,
  ("The Castro", "Alamo Square"): 8,
  ("The Castro", "Golden Gate Park"): 11,
  ("The Castro", "Bayview"): 19,
  ("The Castro", "Sunset District"): 17,
  ("The Castro", "Haight-Ashbury"): 6,
  ("The Castro", "Nob Hill"): 16,
  
  ("Bayview", "Russian Hill"): 23,
  ("Bayview", "Marina District"): 27,
  ("Bayview", "Financial District"): 19,
  ("Bayview", "Alamo Square"): 16,
  ("Bayview", "Golden Gate Park"): 22,
  ("Bayview", "The Castro"): 19,
  ("Bayview", "Sunset District"): 23,
  ("Bayview", "Haight-Ashbury"): 19,
  ("Bayview", "Nob Hill"): 20,
  
  ("Sunset District", "Russian Hill"): 24,
  ("Sunset District", "Marina District"): 21,
  ("Sunset District", "Financial District"): 30,
  ("Sunset District", "Alamo Square"): 17,
  ("Sunset District", "Golden Gate Park"): 11,
  ("Sunset District", "The Castro"): 17,
  ("Sunset District", "Bayview"): 22,
  ("Sunset District", "Haight-Ashbury"): 15,
  ("Sunset District", "Nob Hill"): 27,
  
  ("Haight-Ashbury", "Russian Hill"): 17,
  ("Haight-Ashbury", "Marina District"): 17,
  ("Haight-Ashbury", "Financial District"): 21,
  ("Haight-Ashbury", "Alamo Square"): 5,
  ("Haight-Ashbury", "Golden Gate Park"): 7,
  ("Haight-Ashbury", "The Castro"): 6,
  ("Haight-Ashbury", "Bayview"): 18,
  ("Haight-Ashbury", "Sunset District"): 15,
  ("Haight-Ashbury", "Nob Hill"): 15,
  
  ("Nob Hill", "Russian Hill"): 5,
  ("Nob Hill", "Marina District"): 11,
  ("Nob Hill", "Financial District"): 9,
  ("Nob Hill", "Alamo Square"): 11,
  ("Nob Hill", "Golden Gate Park"): 17,
  ("Nob Hill", "The Castro"): 17,
  ("Nob Hill", "Bayview"): 19,
  ("Nob Hill", "Sunset District"): 24,
  ("Nob Hill", "Haight-Ashbury"): 13
}

# Meeting constraints for each friend with their location, available time window, and minimum meeting duration (in minutes)
meetings = [
    {"person": "Mark", "location": "Marina District", "avail_start": "18:45", "avail_end": "21:00", "duration": 90},
    {"person": "Karen", "location": "Financial District", "avail_start": "9:30", "avail_end": "12:45", "duration": 90},
    {"person": "Barbara", "location": "Alamo Square", "avail_start": "10:00", "avail_end": "19:30", "duration": 90},
    {"person": "Nancy", "location": "Golden Gate Park", "avail_start": "16:45", "avail_end": "20:00", "duration": 105},
    {"person": "David", "location": "The Castro", "avail_start": "9:00", "avail_end": "18:00", "duration": 120},
    {"person": "Linda", "location": "Bayview", "avail_start": "18:15", "avail_end": "19:45", "duration": 45},
    {"person": "Kevin", "location": "Sunset District", "avail_start": "10:00", "avail_end": "17:45", "duration": 120},
    {"person": "Matthew", "location": "Haight-Ashbury", "avail_start": "10:15", "avail_end": "15:30", "duration": 45},
    {"person": "Andrew", "location": "Nob Hill", "avail_start": "11:45", "avail_end": "16:45", "duration": 105}
]

# Convert meeting time windows to minutes from midnight.
for meeting in meetings:
    meeting["avail_start"] = parse_time(meeting["avail_start"])
    meeting["avail_end"] = parse_time(meeting["avail_end"])

# Global best schedule (list of itinerary items) and best count of meetings scheduled.
best_schedule = []
best_count = 0

# Depth-first search/backtracking to explore possible meeting orders.
def dfs(current_loc, current_time, remaining, schedule):
    global best_schedule, best_count
    # Update best schedule if current schedule has more meetings.
    if len(schedule) > best_count:
        best_count = len(schedule)
        best_schedule = schedule[:]
    # Prune if even scheduling all remaining meetings would not beat best_count.
    if len(schedule) + len(remaining) <= best_count:
        return
    # Try scheduling each remaining meeting as next.
    for i, meet in enumerate(remaining):
        key = (current_loc, meet["location"])
        if key not in travel:
            continue  # skip if no travel info (should not happen)
        travel_time = travel[key]
        arrival = current_time + travel_time
        # The meeting can only start when you arrive and when the meeting's window opens.
        start_meet = max(arrival, meet["avail_start"])
        finish = start_meet + meet["duration"]
        # Check if the meeting can be finished within the friend’s available window.
        if finish <= meet["avail_end"]:
            item = {
                "action": "meet",
                "location": meet["location"],
                "person": meet["person"],
                "start_time": format_time(start_meet),
                "end_time": format_time(finish)
            }
            new_remaining = remaining[:i] + remaining[i+1:]
            dfs(meet["location"], finish, new_remaining, schedule + [item])

# Start planning. You arrive at Russian Hill at 9:00 AM (540 minutes after midnight).
dfs("Russian Hill", 540, meetings, [])

# Prepare the result in JSON format.
result = { "itinerary": best_schedule }

# Output the result as JSON.
print(json.dumps(result, indent=2))