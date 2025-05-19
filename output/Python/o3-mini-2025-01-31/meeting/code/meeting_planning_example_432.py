#!/usr/bin/env python3
import json
from copy import deepcopy

# Helper: convert minutes-since-midnight to H:MM string (24-hour format with no leading zero for hour)
def minutes_to_str(t):
    hour = t // 60
    minute = t % 60
    return f"{hour}:{minute:02d}"

# Data definitions for meetings and travel times.
# All times are in minutes since midnight.
# Starting state
start_time = 9 * 60  # 9:00 at Golden Gate Park
start_location = "Golden Gate Park"

# Meeting definitions:
meetings = {
    "Joseph": {
        "location": "Fisherman's Wharf",
        "avail_start": 8 * 60,         # 8:00 -> 480
        "avail_end": 17 * 60 + 30,       # 17:30 -> 1050
        "duration": 90
    },
    "Jeffrey": {
        "location": "Bayview",
        "avail_start": 17 * 60 + 30,     # 17:30 -> 1050
        "avail_end": 21 * 60 + 30,       # 21:30 -> 1290
        "duration": 60
    },
    "Kevin": {
        "location": "Mission District",
        "avail_start": 11 * 60 + 15,     # 11:15 -> 675
        "avail_end": 15 * 60 + 15,       # 15:15 -> 915
        "duration": 30
    },
    "David": {
        "location": "Embarcadero",
        "avail_start": 8 * 60 + 15,      # 8:15 -> 495
        "avail_end": 9 * 60,             # 9:00 -> 540
        "duration": 30
    },
    "Barbara": {
        "location": "Financial District",
        "avail_start": 10 * 60 + 30,     # 10:30 -> 630
        "avail_end": 16 * 60 + 30,       # 16:30 -> 990
        "duration": 15
    }
}

# Travel times in minutes: dictionary with keys (origin, destination)
travel_times = {
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Financial District"): 26,
    
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Financial District"): 11,
    
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Financial District"): 19,
    
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Bayview"): 15,
    ("Mission District", "Embarcadero"): 19,
    ("Mission District", "Financial District"): 17,
    
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Mission District"): 20,
    ("Embarcadero", "Financial District"): 5,
    
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Embarcadero"): 4
}

# Backtracking search for an optimal meeting schedule.
# The goal is to maximize the number of meetings (friends met).
best_schedule = []
best_count = 0

def search(current_time, current_location, scheduled, remaining):
    global best_schedule, best_count

    # If no more meetings to schedule, update best if needed.
    if len(scheduled) > best_count:
        best_schedule = deepcopy(scheduled)
        best_count = len(scheduled)
    # Try all remaining meetings
    for person in list(remaining.keys()):
        meeting = remaining[person]
        # Check travel time from current location to meeting location.
        if (current_location, meeting["location"]) not in travel_times:
            continue  # no route if missing
        travel = travel_times[(current_location, meeting["location"])]
        arrival_time = current_time + travel
        # Determine meeting start time: maximum of arrival or person's available start.
        meeting_start = max(arrival_time, meeting["avail_start"])
        meeting_end = meeting_start + meeting["duration"]
        # Check if meeting can be held within availability window.
        if meeting_end <= meeting["avail_end"]:
            # Proceed: schedule this meeting.
            scheduled.append({
                "person": person,
                "location": meeting["location"],
                "start_time": meeting_start,
                "end_time": meeting_end
            })
            # Remove this meeting from remaining.
            next_remaining = deepcopy(remaining)
            del next_remaining[person]
            search(meeting_end, meeting["location"], scheduled, next_remaining)
            # Backtrack.
            scheduled.pop()

# Start recursive search from the starting location and time with all meetings available.
search(start_time, start_location, [], meetings)

# The best_schedule now contains the optimal meeting events in order.
# Format the best_schedule as JSON with time strings.
itinerary = []
for event in best_schedule:
    itinerary.append({
        "action": "meet",
        "location": event["location"],
        "person": event["person"],
        "start_time": minutes_to_str(event["start_time"]),
        "end_time": minutes_to_str(event["end_time"])
    })

result = {"itinerary": itinerary}

# Output the result as JSON.
print(json.dumps(result, indent=2))
    
if __name__ == '__main__':
    pass