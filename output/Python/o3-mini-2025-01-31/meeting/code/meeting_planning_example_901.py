#!/usr/bin/env python3
import json
import sys

# Utility functions to convert between "H:MM" and minutes since midnight
def time_to_minutes(t):
    # t is a string in "H:MM" (24-hour format, no leading zeros assumed)
    parts = t.split(":")
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

# Define travel times as a nested dictionary: travel_times[from_location][to_location] = minutes
travel_times = {
    "Russian Hill": {
        "Pacific Heights": 7,
        "North Beach": 5,
        "Golden Gate Park": 21,
        "Embarcadero": 8,
        "Haight-Ashbury": 17,
        "Fisherman's Wharf": 7,
        "Mission District": 16,
        "Alamo Square": 15,
        "Bayview": 23,
        "Richmond District": 14,
    },
    "Pacific Heights": {
        "Russian Hill": 7,
        "North Beach": 9,
        "Golden Gate Park": 15,
        "Embarcadero": 10,
        "Haight-Ashbury": 11,
        "Fisherman's Wharf": 13,
        "Mission District": 15,
        "Alamo Square": 10,
        "Bayview": 22,
        "Richmond District": 12,
    },
    "North Beach": {
        "Russian Hill": 4,
        "Pacific Heights": 8,
        "Golden Gate Park": 22,
        "Embarcadero": 6,
        "Haight-Ashbury": 18,
        "Fisherman's Wharf": 5,
        "Mission District": 18,
        "Alamo Square": 16,
        "Bayview": 25,
        "Richmond District": 18,
    },
    "Golden Gate Park": {
        "Russian Hill": 19,
        "Pacific Heights": 16,
        "North Beach": 23,
        "Embarcadero": 25,
        "Haight-Ashbury": 7,
        "Fisherman's Wharf": 24,
        "Mission District": 17,
        "Alamo Square": 9,
        "Bayview": 23,
        "Richmond District": 7,
    },
    "Embarcadero": {
        "Russian Hill": 8,
        "Pacific Heights": 11,
        "North Beach": 5,
        "Golden Gate Park": 25,
        "Haight-Ashbury": 21,
        "Fisherman's Wharf": 6,
        "Mission District": 20,
        "Alamo Square": 19,
        "Bayview": 21,
        "Richmond District": 21,
    },
    "Haight-Ashbury": {
        "Russian Hill": 17,
        "Pacific Heights": 12,
        "North Beach": 19,
        "Golden Gate Park": 7,
        "Embarcadero": 20,
        "Fisherman's Wharf": 23,
        "Mission District": 11,
        "Alamo Square": 5,
        "Bayview": 18,
        "Richmond District": 10,
    },
    "Fisherman's Wharf": {
        "Russian Hill": 7,
        "Pacific Heights": 12,
        "North Beach": 6,
        "Golden Gate Park": 25,
        "Embarcadero": 8,
        "Haight-Ashbury": 22,
        "Mission District": 22,
        "Alamo Square": 21,
        "Bayview": 26,
        "Richmond District": 18,
    },
    "Mission District": {
        "Russian Hill": 15,
        "Pacific Heights": 16,
        "North Beach": 17,
        "Golden Gate Park": 17,
        "Embarcadero": 19,
        "Haight-Ashbury": 12,
        "Fisherman's Wharf": 22,
        "Alamo Square": 11,
        "Bayview": 14,
        "Richmond District": 20,
    },
    "Alamo Square": {
        "Russian Hill": 13,
        "Pacific Heights": 10,
        "North Beach": 15,
        "Golden Gate Park": 9,
        "Embarcadero": 16,
        "Haight-Ashbury": 5,
        "Fisherman's Wharf": 19,
        "Mission District": 10,
        "Bayview": 16,
        "Richmond District": 11,
    },
    "Bayview": {
        "Russian Hill": 23,
        "Pacific Heights": 23,
        "North Beach": 22,
        "Golden Gate Park": 22,
        "Embarcadero": 19,
        "Haight-Ashbury": 19,
        "Fisherman's Wharf": 25,
        "Mission District": 13,
        "Alamo Square": 16,
        "Richmond District": 25,
    },
    "Richmond District": {
        "Russian Hill": 13,
        "Pacific Heights": 10,
        "North Beach": 17,
        "Golden Gate Park": 9,
        "Embarcadero": 19,
        "Haight-Ashbury": 10,
        "Fisherman's Wharf": 18,
        "Mission District": 20,
        "Alamo Square": 13,
        "Bayview": 27,
    }
}

# Define meeting constraints data
# Each meeting: name, location, avail_start, avail_end, min_duration
meetings = [
    {
        "person": "Emily",
        "location": "Pacific Heights",
        "avail_start": time_to_minutes("9:15"),
        "avail_end": time_to_minutes("13:45"),
        "min_duration": 120,
    },
    {
        "person": "Helen",
        "location": "North Beach",
        "avail_start": time_to_minutes("13:45"),
        "avail_end": time_to_minutes("18:45"),
        "min_duration": 30,
    },
    {
        "person": "Kimberly",
        "location": "Golden Gate Park",
        "avail_start": time_to_minutes("18:45"),
        "avail_end": time_to_minutes("21:15"),
        "min_duration": 75,
    },
    {
        "person": "James",
        "location": "Embarcadero",
        "avail_start": time_to_minutes("10:30"),
        "avail_end": time_to_minutes("11:30"),
        "min_duration": 30,
    },
    {
        "person": "Linda",
        "location": "Haight-Ashbury",
        "avail_start": time_to_minutes("7:30"),
        "avail_end": time_to_minutes("19:15"),
        "min_duration": 15,
    },
    {
        "person": "Paul",
        "location": "Fisherman's Wharf",
        "avail_start": time_to_minutes("14:45"),
        "avail_end": time_to_minutes("18:45"),
        "min_duration": 90,
    },
    {
        "person": "Anthony",
        "location": "Mission District",
        "avail_start": time_to_minutes("8:00"),
        "avail_end": time_to_minutes("14:45"),
        "min_duration": 105,
    },
    {
        "person": "Nancy",
        "location": "Alamo Square",
        "avail_start": time_to_minutes("8:30"),
        "avail_end": time_to_minutes("13:45"),
        "min_duration": 120,
    },
    {
        "person": "William",
        "location": "Bayview",
        "avail_start": time_to_minutes("17:30"),
        "avail_end": time_to_minutes("20:30"),
        "min_duration": 120,
    },
    {
        "person": "Margaret",
        "location": "Richmond District",
        "avail_start": time_to_minutes("15:15"),
        "avail_end": time_to_minutes("18:15"),
        "min_duration": 45,
    }
]

# Starting point and time
start_location = "Russian Hill"
start_time = time_to_minutes("9:00")

# Global best result: maximum number of meetings scheduled
best_schedule = []
best_count = 0

def dfs(current_time, current_location, remaining, schedule):
    global best_schedule, best_count

    # Update best schedule if current schedule has more meetings
    if len(schedule) > best_count:
        best_count = len(schedule)
        best_schedule = schedule.copy()
    # Try each remaining meeting
    for i, meeting in enumerate(remaining):
        # Get travel time from current location to meeting location
        # It is possible that current_location equals meeting location? But in our case, start might be different.
        travel = travel_times.get(current_location, {}).get(meeting["location"], None)
        if travel is None:
            continue  # no route available
        # Earliest arrival time at meeting location
        arrival_time = current_time + travel
        # The meeting can only start when the friend is available
        meeting_start = max(arrival_time, meeting["avail_start"])
        meeting_end = meeting_start + meeting["min_duration"]
        # Check if meeting can be completed within available window
        if meeting_end <= meeting["avail_end"]:
            # Proceed with this meeting scheduled
            new_schedule = schedule.copy()
            new_schedule.append({
                "action": "meet",
                "location": meeting["location"],
                "person": meeting["person"],
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            })
            new_remaining = remaining[:i] + remaining[i+1:]
            dfs(meeting_end, meeting["location"], new_remaining, new_schedule)

# Run DFS from starting state
dfs(start_time, start_location, meetings, [])

# Prepare the result in the required JSON format
result = {"itinerary": best_schedule}

# Output JSON formatted result
print(json.dumps(result, indent=2))
    
if __name__ == '__main__':
    sys.exit(0)