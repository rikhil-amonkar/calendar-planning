#!/usr/bin/env python3
import json
import copy

# Helper function to convert minutes to "H:MM" 24-hour formatted string (no leading zero in hour)
def format_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Define travel times (in minutes) as a dict of dicts.
travel_times = {
    "Pacific Heights": {
        "Marina District": 6,
        "The Castro": 16,
        "Richmond District": 12,
        "Alamo Square": 10,
        "Financial District": 13,
        "Presidio": 11,
        "Mission District": 15,
        "Nob Hill": 8,
        "Russian Hill": 7
    },
    "Marina District": {
        "Pacific Heights": 7,
        "The Castro": 22,
        "Richmond District": 11,
        "Alamo Square": 15,
        "Financial District": 17,
        "Presidio": 10,
        "Mission District": 20,
        "Nob Hill": 12,
        "Russian Hill": 8
    },
    "The Castro": {
        "Pacific Heights": 16,
        "Marina District": 21,
        "Richmond District": 16,
        "Alamo Square": 8,
        "Financial District": 21,
        "Presidio": 20,
        "Mission District": 7,
        "Nob Hill": 16,
        "Russian Hill": 18
    },
    "Richmond District": {
        "Pacific Heights": 10,
        "Marina District": 9,
        "The Castro": 16,
        "Alamo Square": 13,
        "Financial District": 22,
        "Presidio": 7,
        "Mission District": 20,
        "Nob Hill": 17,
        "Russian Hill": 13
    },
    "Alamo Square": {
        "Pacific Heights": 10,
        "Marina District": 15,
        "The Castro": 8,
        "Richmond District": 11,
        "Financial District": 17,
        "Presidio": 17,
        "Mission District": 10,
        "Nob Hill": 11,
        "Russian Hill": 13
    },
    "Financial District": {
        "Pacific Heights": 13,
        "Marina District": 15,
        "The Castro": 20,
        "Richmond District": 21,
        "Alamo Square": 17,
        "Presidio": 22,
        "Mission District": 17,
        "Nob Hill": 8,
        "Russian Hill": 11
    },
    "Presidio": {
        "Pacific Heights": 11,
        "Marina District": 11,
        "The Castro": 21,
        "Richmond District": 7,
        "Alamo Square": 19,
        "Financial District": 23,
        "Mission District": 26,
        "Nob Hill": 18,
        "Russian Hill": 14
    },
    "Mission District": {
        "Pacific Heights": 16,
        "Marina District": 19,
        "The Castro": 7,
        "Richmond District": 20,
        "Alamo Square": 11,
        "Financial District": 15,
        "Presidio": 25,
        "Nob Hill": 12,
        "Russian Hill": 15
    },
    "Nob Hill": {
        "Pacific Heights": 8,
        "Marina District": 11,
        "The Castro": 17,
        "Richmond District": 14,
        "Alamo Square": 11,
        "Financial District": 9,
        "Presidio": 17,
        "Mission District": 13,
        "Russian Hill": 5
    },
    "Russian Hill": {
        "Pacific Heights": 7,
        "Marina District": 7,
        "The Castro": 21,
        "Richmond District": 14,
        "Alamo Square": 15,
        "Financial District": 11,
        "Presidio": 14,
        "Mission District": 16,
        "Nob Hill": 5
    }
}

# Define the meeting constraints.
# Times are in minutes from midnight.
# 9:00 AM = 540 minutes.
meetings = [
    {
        "person": "Linda",
        "location": "Marina District",
        "avail_start": 18*60,          # 18:00 = 1080
        "avail_end": 22*60,            # 22:00 = 1320
        "duration": 30
    },
    {
        "person": "Kenneth",
        "location": "The Castro",
        "avail_start": 14*60 + 45,     # 14:45 = 885
        "avail_end": 16*60 + 15,       # 16:15 = 975
        "duration": 30
    },
    {
        "person": "Kimberly",
        "location": "Richmond District",
        "avail_start": 14*60 + 15,     # 14:15 = 855
        "avail_end": 22*60,            # 22:00 = 1320
        "duration": 30
    },
    {
        "person": "Paul",
        "location": "Alamo Square",
        "avail_start": 21*60,          # 21:00 = 1260
        "avail_end": 21*60 + 30,       # 21:30 = 1290
        "duration": 15
    },
    {
        "person": "Carol",
        "location": "Financial District",
        "avail_start": 10*60 + 15,     # 10:15 = 615
        "avail_end": 12*60,            # 12:00 = 720
        "duration": 60
    },
    {
        "person": "Brian",
        "location": "Presidio",
        "avail_start": 10*60,          # 10:00 = 600
        "avail_end": 21*60 + 30,       # 21:30 = 1290
        "duration": 75
    },
    {
        "person": "Laura",
        "location": "Mission District",
        "avail_start": 16*60 + 15,     # 16:15 = 975
        "avail_end": 20*60 + 30,       # 20:30 = 1230
        "duration": 30
    },
    {
        "person": "Sandra",
        "location": "Nob Hill",
        "avail_start": 9*60 + 15,      # 9:15 = 555
        "avail_end": 18*60 + 30,       # 18:30 = 1110
        "duration": 60
    },
    {
        "person": "Karen",
        "location": "Russian Hill",
        "avail_start": 18*60 + 30,     # 18:30 = 1110
        "avail_end": 22*60,            # 22:00 = 1320
        "duration": 75
    }
]

# Global variables to track the best schedule (maximizing number of meetings)
best_schedule = []
best_count = 0

# Depth-first search to try all orders of meetings that are feasible.
def dfs(current_time, current_location, remaining_meetings, schedule):
    global best_schedule, best_count

    # Update best schedule if current schedule has more meetings.
    if len(schedule) > best_count:
        best_count = len(schedule)
        best_schedule = schedule

    # Try to schedule each remaining meeting next.
    for i, meet in enumerate(remaining_meetings):
        # Calculate travel time from current location to the meeting's location.
        travel = travel_times[current_location][meet["location"]]
        arrival = current_time + travel
        # Meeting can only start at the later of arrival and the meeting's available start time.
        meeting_start = max(arrival, meet["avail_start"])
        meeting_end = meeting_start + meet["duration"]
        # Check if meeting can finish within the person's available window.
        if meeting_end <= meet["avail_end"]:
            # Create an action entry for this meeting.
            action = {
                "action": "meet",
                "location": meet["location"],
                "person": meet["person"],
                "start_time": format_time(meeting_start),
                "end_time": format_time(meeting_end)
            }
            # Build a new schedule with this meeting.
            new_schedule = schedule + [action]
            # Prepare a new list of remaining meetings without the current one.
            new_remaining = remaining_meetings[:i] + remaining_meetings[i+1:]
            # Recurse with updated current time and location.
            dfs(meeting_end, meet["location"], new_remaining, new_schedule)

if __name__ == "__main__":
    # Starting location and time.
    # You arrive at Pacific Heights at 9:00AM (540 minutes after midnight)
    start_time = 9 * 60  # 540 minutes
    start_location = "Pacific Heights"
    
    # Run DFS search for an optimal schedule.
    dfs(start_time, start_location, meetings, [])
    
    # Build the result dictionary with the itinerary.
    result = {
        "itinerary": best_schedule
    }
    
    # Output the result as a JSON formatted dictionary.
    print(json.dumps(result, indent=2))