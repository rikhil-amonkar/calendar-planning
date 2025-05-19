#!/usr/bin/env python3
import json
from itertools import permutations

# Helper function: convert minutes since midnight to H:MM (24-hour) format
def format_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Travel times in minutes between locations (as provided)
travel_times = {
    "Financial District": {
        "Golden Gate Park": 23,
        "Chinatown": 5,
        "Union Square": 9,
        "Fisherman's Wharf": 10,
        "Pacific Heights": 13,
        "North Beach": 7
    },
    "Golden Gate Park": {
        "Financial District": 26,
        "Chinatown": 23,
        "Union Square": 22,
        "Fisherman's Wharf": 24,
        "Pacific Heights": 16,
        "North Beach": 24
    },
    "Chinatown": {
        "Financial District": 5,
        "Golden Gate Park": 23,
        "Union Square": 7,
        "Fisherman's Wharf": 8,
        "Pacific Heights": 10,
        "North Beach": 3
    },
    "Union Square": {
        "Financial District": 9,
        "Golden Gate Park": 22,
        "Chinatown": 7,
        "Fisherman's Wharf": 15,
        "Pacific Heights": 15,
        "North Beach": 10
    },
    "Fisherman's Wharf": {
        "Financial District": 11,
        "Golden Gate Park": 25,
        "Chinatown": 12,
        "Union Square": 13,
        "Pacific Heights": 12,
        "North Beach": 6
    },
    "Pacific Heights": {
        "Financial District": 13,
        "Golden Gate Park": 15,
        "Chinatown": 11,
        "Union Square": 12,
        "Fisherman's Wharf": 13,
        "North Beach": 9
    },
    "North Beach": {
        "Financial District": 8,
        "Golden Gate Park": 22,
        "Chinatown": 6,
        "Union Square": 7,
        "Fisherman's Wharf": 5,
        "Pacific Heights": 8
    }
}

# Define friend meeting constraints.
# All times are in minutes since midnight.
friends = {
    "Stephanie": {
        "location": "Golden Gate Park",
        "available_start": 11 * 60,       # 11:00 -> 660
        "available_end": 15 * 60,         # 15:00 -> 900
        "duration": 105
    },
    "Karen": {
        "location": "Chinatown",
        "available_start": 13 * 60 + 45,  # 13:45 -> 825
        "available_end": 16 * 60 + 30,    # 16:30 -> 990
        "duration": 15
    },
    "Brian": {
        "location": "Union Square",
        "available_start": 15 * 60,       # 15:00 -> 900
        "available_end": 17 * 60 + 15,    # 17:15 -> 1035
        "duration": 30
    },
    "Rebecca": {
        "location": "Fisherman's Wharf",
        "available_start": 8 * 60,       # 8:00 -> 480
        "available_end": 11 * 60 + 15,   # 11:15 -> 675
        "duration": 30
    },
    "Joseph": {
        "location": "Pacific Heights",
        "available_start": 8 * 60 + 15,  # 8:15 -> 495
        "available_end": 9 * 60 + 30,    # 9:30 -> 570
        "duration": 60
    },
    "Steven": {
        "location": "North Beach",
        "available_start": 14 * 60 + 30, # 14:30 -> 870
        "available_end": 20 * 60 + 45,   # 20:45 -> 1245
        "duration": 120
    }
}

# Starting conditions: Arrive at Financial District at 9:00AM
start_location = "Financial District"
start_time = 9 * 60  # 9:00 -> 540 minutes

# Use backtracking to find the optimal (maximum meetings) schedule.
best_schedule = []

def backtrack(current_location, current_time, remaining, schedule):
    global best_schedule
    # Update best_schedule if current schedule has more meetings
    if len(schedule) > len(best_schedule):
        best_schedule = schedule.copy()
    
    for friend in list(remaining):
        details = friends[friend]
        # If current_location is the same as friend's location, travel time is 0.
        if current_location == details["location"]:
            travel = 0
        else:
            travel = travel_times[current_location][details["location"]]
        arrival_time = current_time + travel
        meeting_start = max(arrival_time, details["available_start"])
        meeting_end = meeting_start + details["duration"]
        # Check if meeting can finish before friend leaves.
        if meeting_end <= details["available_end"]:
            # Append meeting event to schedule.
            meeting = {
                "person": friend,
                "location": details["location"],
                "start": meeting_start,
                "end": meeting_end
            }
            new_schedule = schedule.copy()
            new_schedule.append(meeting)
            new_remaining = remaining.copy()
            new_remaining.remove(friend)
            backtrack(details["location"], meeting_end, new_remaining, new_schedule)

# Prepare list of friend names.
friend_names = list(friends.keys())
backtrack(start_location, start_time, set(friend_names), [])

# Build the itinerary in the expected JSON format using the best_schedule.
itinerary = []
# Reconstruct the meeting events with proper formatted times.
current_loc = start_location
current_t = start_time

for event in best_schedule:
    details = friends[event["person"]]
    # Compute travel time from current location to friend's location (if different)
    if current_loc == details["location"]:
        travel = 0
    else:
        travel = travel_times[current_loc][details["location"]]
    arrival_time = current_t + travel
    meeting_start = max(arrival_time, details["available_start"])
    meeting_end = meeting_start + details["duration"]
    itinerary.append({
        "action": "meet",
        "location": details["location"],
        "person": event["person"],
        "start_time": format_time(meeting_start),
        "end_time": format_time(meeting_end)
    })
    current_loc = details["location"]
    current_t = meeting_end

output = {"itinerary": itinerary}

print(json.dumps(output, indent=2))