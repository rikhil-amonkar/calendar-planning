#!/usr/bin/env python3
import json
import itertools

# Helper function to convert minutes since midnight into "H:MM" format
def minutes_to_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times (in minutes) between locations
travel_times = {
    "Fisherman's Wharf": {
        "Bayview": 26,
        "Golden Gate Park": 25,
        "Nob Hill": 11,
        "Marina District": 9,
        "Embarcadero": 8
    },
    "Bayview": {
        "Fisherman's Wharf": 25,
        "Golden Gate Park": 22,
        "Nob Hill": 20,
        "Marina District": 25,
        "Embarcadero": 19
    },
    "Golden Gate Park": {
        "Fisherman's Wharf": 24,
        "Bayview": 23,
        "Nob Hill": 20,
        "Marina District": 16,
        "Embarcadero": 25
    },
    "Nob Hill": {
        "Fisherman's Wharf": 11,
        "Bayview": 19,
        "Golden Gate Park": 17,
        "Marina District": 11,
        "Embarcadero": 9
    },
    "Marina District": {
        "Fisherman's Wharf": 10,
        "Bayview": 27,
        "Golden Gate Park": 18,
        "Nob Hill": 12,
        "Embarcadero": 14
    },
    "Embarcadero": {
        "Fisherman's Wharf": 6,
        "Bayview": 21,
        "Golden Gate Park": 25,
        "Nob Hill": 10,
        "Marina District": 12
    }
}

# Define meeting constraints.
# Times are represented as minutes since midnight.
# 9:00 AM = 540, 8:45 AM = 525, 16:15 = 975, 15:30 = 930, 18:30 = 1110, 17:30 = 1050, 22:00 = 1320,
# 18:45 = 1125, 21:45 = 1305.
meetings = [
    {
        "name": "Thomas",
        "location": "Bayview",
        "avail_start": 15 * 60 + 30,  # 15:30 (930)
        "avail_end": 18 * 60 + 30,    # 18:30 (1110)
        "min_duration": 120         # 120 minutes required
    },
    {
        "name": "Stephanie",
        "location": "Golden Gate Park",
        "avail_start": 18 * 60 + 30,  # 18:30 (1110)
        "avail_end": 21 * 60 + 45,    # 21:45 (1305)
        "min_duration": 30          # 30 minutes required
    },
    {
        "name": "Laura",
        "location": "Nob Hill",
        "avail_start": 8 * 60 + 45,   # 8:45 (525)
        "avail_end": 16 * 60 + 15,    # 16:15 (975)
        "min_duration": 30          # 30 minutes required
    },
    {
        "name": "Betty",
        "location": "Marina District",
        "avail_start": 18 * 60 + 45,  # 18:45 (1125)
        "avail_end": 21 * 60 + 45,    # 21:45 (1305)
        "min_duration": 45          # 45 minutes required
    },
    {
        "name": "Patricia",
        "location": "Embarcadero",
        "avail_start": 17 * 60 + 30,  # 17:30 (1050)
        "avail_end": 22 * 60 + 0,     # 22:00 (1320)
        "min_duration": 45          # 45 minutes required
    }
]

# Starting conditions: You arrive at Fisherman's Wharf at 9:00 AM (540 minutes)
start_time = 9 * 60      # 9:00 AM -> 540 minutes
start_location = "Fisherman's Wharf"

# Simulation function: Given an order of meetings, compute the resulting schedule.
def simulate_schedule(order, current_time, current_location):
    itinerary = []
    for meeting in order:
        # Calculate arrival time from current location to meeting location
        travel = travel_times[current_location][meeting["location"]]
        arrival = current_time + travel
        # Meeting cannot start before the friend's availability
        meeting_start = max(arrival, meeting["avail_start"])
        meeting_end = meeting_start + meeting["min_duration"]
        # Check if the meeting can finish before the friend's availability ends
        if meeting_end > meeting["avail_end"]:
            # Cannot schedule this meeting; break out of the loop.
            break
        # Append the meeting event
        event = {
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["name"],
            "start_time": minutes_to_str(meeting_start),
            "end_time": minutes_to_str(meeting_end)
        }
        itinerary.append(event)
        # Update current time and location after finishing the meeting
        current_time = meeting_end
        current_location = meeting["location"]
    return len(itinerary), current_time, itinerary

# Brute-force search over all permutations of the meetings.
# The goal is to maximize the number of meetings scheduled.
best_itinerary = []
max_meetings = -1
best_finish_time = None

for order in itertools.permutations(meetings):
    count, finish_time, itinerary = simulate_schedule(order, start_time, start_location)
    # Check if this order schedules more meetings
    if count > max_meetings:
        max_meetings = count
        best_finish_time = finish_time
        best_itinerary = itinerary
    # Tie-break: if same number of meetings, choose the schedule with the earlier finish time.
    elif count == max_meetings and count > 0:
        if finish_time < best_finish_time:
            best_finish_time = finish_time
            best_itinerary = itinerary

# Prepare the result as a JSON-formatted dictionary
result = {"itinerary": best_itinerary}

# Output the result as JSON
print(json.dumps(result))