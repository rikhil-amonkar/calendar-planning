#!/usr/bin/env python3
import itertools
import json

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Define travel times in minutes between locations
travel_times = {
    "Bayview": {
        "Embarcadero": 19,
        "Richmond District": 25,
        "Fisherman's Wharf": 25
    },
    "Embarcadero": {
        "Bayview": 21,
        "Richmond District": 21,
        "Fisherman's Wharf": 6
    },
    "Richmond District": {
        "Bayview": 26,
        "Embarcadero": 19,
        "Fisherman's Wharf": 18
    },
    "Fisherman's Wharf": {
        "Bayview": 26,
        "Embarcadero": 8,
        "Richmond District": 18
    }
}

# Meeting constraints: times are in minutes since midnight.
# 9:00 AM = 9 * 60 = 540
# Jessica: 16:45 = 16*60+45 = 1005, 19:00 = 1140, min meeting time = 30
# Sandra: 18:30 = 18*60+30 = 1110, 21:45 = 1305, min meeting time = 120
# Jason: 16:00 = 960, 16:45 = 1005, min meeting time = 30

meetings = [
    {
        "person": "Jessica",
        "location": "Embarcadero",
        "avail_start": 16 * 60 + 45,  # 16:45 -> 1005 minutes
        "avail_end": 19 * 60,         # 19:00 -> 1140 minutes
        "min_duration": 30
    },
    {
        "person": "Sandra",
        "location": "Richmond District",
        "avail_start": 18 * 60 + 30,  # 18:30 -> 1110 minutes
        "avail_end": 21 * 60 + 45,    # 21:45 -> 1305 minutes
        "min_duration": 120
    },
    {
        "person": "Jason",
        "location": "Fisherman's Wharf",
        "avail_start": 16 * 60,       # 16:00 -> 960 minutes
        "avail_end": 16 * 60 + 45,     # 16:45 -> 1005 minutes
        "min_duration": 30
    }
]

# Starting point: arrive at Bayview at 9:00 AM (540 minutes)
starting_location = "Bayview"
starting_time = 9 * 60  # 9:00 AM

def compute_schedule(order):
    current_time = starting_time
    current_location = starting_location
    schedule = []
    
    for meeting in order:
        # Compute travel time from current location to the meeting location.
        travel_time = travel_times[current_location][meeting["location"]]
        arrival_time = current_time + travel_time
        # The meeting can only start when both you have arrived and the friend is available.
        meeting_start = max(arrival_time, meeting["avail_start"])
        meeting_end = meeting_start + meeting["min_duration"]
        # Check if the meeting can be completed within the friend's availability window.
        if meeting_end > meeting["avail_end"]:
            return None  # This order is not feasible.
        
        schedule.append({
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["person"],
            "start_time": minutes_to_time_str(meeting_start),
            "end_time": minutes_to_time_str(meeting_end)
        })
        
        # Update current time and location.
        current_time = meeting_end
        current_location = meeting["location"]
    
    return schedule

# Try all possible orders and choose the one with the most meetings scheduled.
best_schedule = None
max_meetings = 0
best_finish_time = None

for order in itertools.permutations(meetings):
    schedule = compute_schedule(order)
    if schedule is not None:
        meeting_count = len(schedule)
        # Use finishing time (current_time after last meeting) to break ties.
        last_meeting_end = 0
        # Compute the end time by simulating the schedule again.
        current_time = starting_time
        current_location = starting_location
        for meeting in order:
            travel_time = travel_times[current_location][meeting["location"]]
            arrival_time = current_time + travel_time
            meeting_start = max(arrival_time, meeting["avail_start"])
            meeting_end = meeting_start + meeting["min_duration"]
            current_time = meeting_end
            current_location = meeting["location"]
        last_meeting_end = current_time

        if meeting_count > max_meetings or (meeting_count == max_meetings and (best_finish_time is None or last_meeting_end < best_finish_time)):
            best_schedule = schedule
            max_meetings = meeting_count
            best_finish_time = last_meeting_end

# Prepare the output dictionary
output = {"itinerary": best_schedule if best_schedule is not None else []}

# Output the result as JSON
print(json.dumps(output))