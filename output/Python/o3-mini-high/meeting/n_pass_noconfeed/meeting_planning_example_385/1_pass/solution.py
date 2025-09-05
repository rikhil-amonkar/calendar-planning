#!/usr/bin/env python3
import json

def minutes_to_time_str(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Define travel times (in minutes) between locations
travel_times = {
    "Nob Hill": {
        "Presidio": 17,
        "North Beach": 8,
        "Fisherman's Wharf": 11,
        "Pacific Heights": 8
    },
    "Presidio": {
        "Nob Hill": 18,
        "North Beach": 18,
        "Fisherman's Wharf": 19,
        "Pacific Heights": 11
    },
    "North Beach": {
        "Nob Hill": 7,
        "Presidio": 17,
        "Fisherman's Wharf": 5,
        "Pacific Heights": 8
    },
    "Fisherman's Wharf": {
        "Nob Hill": 11,
        "Presidio": 17,
        "North Beach": 6,
        "Pacific Heights": 12
    },
    "Pacific Heights": {
        "Nob Hill": 8,
        "Presidio": 11,
        "North Beach": 9,
        "Fisherman's Wharf": 13
    }
}

# Meeting constraints for each friend
# Times are stored in minutes since midnight.
friends = [
    {
        "name": "Jeffrey",
        "location": "Presidio",
        "avail_start": 8 * 60,         # 8:00 AM = 480
        "avail_end": 10 * 60,          # 10:00 AM = 600
        "min_duration": 105
    },
    {
        "name": "Steven",
        "location": "North Beach",
        "avail_start": 13 * 60 + 30,   # 13:30 = 810
        "avail_end": 22 * 60,          # 22:00 = 1320
        "min_duration": 45
    },
    {
        "name": "Barbara",
        "location": "Fisherman's Wharf",
        "avail_start": 18 * 60,        # 18:00 = 1080
        "avail_end": 21 * 60 + 30,     # 21:30 = 1290
        "min_duration": 30
    },
    {
        "name": "John",
        "location": "Pacific Heights",
        "avail_start": 9 * 60,         # 9:00 = 540
        "avail_end": 13 * 60 + 30,     # 13:30 = 810
        "min_duration": 15
    }
]

# Starting parameters: you arrive at Nob Hill at 9:00AM.
start_location = "Nob Hill"
start_time = 9 * 60  # 9:00 AM = 540 minutes

# Global variables to track the best schedule found.
best_schedule = []
best_count = 0
best_finish_time = float('inf')

def search(current_time, current_location, remaining_friends, schedule):
    global best_schedule, best_count, best_finish_time
    found_option = False
    for i, friend in enumerate(remaining_friends):
        # Compute travel time from current_location to friend's location.
        travel_time = travel_times[current_location][friend["location"]]
        arrival_time = current_time + travel_time
        # Meeting can only start once the friend is available.
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["min_duration"]
        # Check if the meeting can be completed within the friend's availability window.
        if meeting_end <= friend["avail_end"]:
            meeting_entry = {
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": minutes_to_time_str(meeting_start),
                "end_time": minutes_to_time_str(meeting_end)
            }
            new_schedule = schedule + [meeting_entry]
            new_remaining = remaining_friends[:i] + remaining_friends[i+1:]
            search(meeting_end, friend["location"], new_remaining, new_schedule)
            found_option = True
    # If no further meetings can be scheduled, update best_schedule if this one has more meetings.
    if not found_option:
        current_count = len(schedule)
        if current_count > best_count or (current_count == best_count and current_time < best_finish_time):
            best_count = current_count
            best_finish_time = current_time
            best_schedule = schedule

# Explore all possible meeting orders using recursive search.
search(start_time, start_location, friends, [])

# Prepare the final itinerary result.
result = {"itinerary": best_schedule}
print(json.dumps(result))