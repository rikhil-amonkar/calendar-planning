#!/usr/bin/env python3
import json
import itertools

# Helper functions to convert time in minutes since midnight to formatted H:MM string
def minutes_to_str(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Define travel times in minutes between locations as a dictionary.
# Keys are tuples (from, to)
travel_times = {
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Richmond District"): 7,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Presidio"): 7
}

# Define meeting constraints for each friend.
# Times are given in minutes since midnight.
# For example, 9:00 AM is 9*60 = 540.
meetings = {
    "Melissa": {
        "location": "Golden Gate Park",
        "avail_start": 8*60 + 30,  # 8:30 AM -> 510 minutes
        "avail_end": 20*60,        # 20:00 -> 1200 minutes
        "duration": 15             # 15 minutes minimum meeting
    },
    "Nancy": {
        "location": "Presidio",
        "avail_start": 19*60 + 45, # 19:45 -> 1185 minutes
        "avail_end": 22*60,        # 22:00 -> 1320 minutes
        "duration": 105            # 105 minutes meeting
    },
    "Emily": {
        "location": "Richmond District",
        "avail_start": 16*60 + 45, # 16:45 -> 1005 minutes
        "avail_end": 22*60,        # 22:00 -> 1320 minutes
        "duration": 120            # 120 minutes meeting
    }
}

# Starting point and start time
start_location = "Fisherman's Wharf"
start_time = 9 * 60  # 9:00 AM => 540 minutes

# Function to simulate a given permutation of meetings.
# Returns a tuple (feasible, itinerary, finish_time, total_travel_time)
def simulate_schedule(order):
    itinerary = []
    current_location = start_location
    current_time = start_time
    total_travel = 0

    for person in order:
        details = meetings[person]
        meeting_location = details["location"]
        # Get travel time from current location to meeting location.
        travel = travel_times.get((current_location, meeting_location))
        if travel is None:
            # If not found, then try opposite order or skip (incomplete data)
            return (False, None, None, None)
        # Travel to the meeting location.
        current_time += travel
        total_travel += travel

        # Meeting can only start after the friend's available start time.
        meeting_start = max(current_time, details["avail_start"])
        meeting_end = meeting_start + details["duration"]
        # Check if meeting ends before friend's available end.
        if meeting_end > details["avail_end"]:
            return (False, None, None, None)

        # Append meeting event to itinerary.
        itinerary.append({
            "action": "meet",
            "location": meeting_location,
            "person": person,
            "start_time": minutes_to_str(meeting_start),
            "end_time": minutes_to_str(meeting_end)
        })

        # Update current time and current location.
        current_time = meeting_end
        current_location = meeting_location

    return (True, itinerary, current_time, total_travel)

# Evaluate all possible orders (permutations) of meeting with Melissa, Nancy, and Emily.
possible_orders = list(itertools.permutations(meetings.keys()))
feasible_schedules = []

for order in possible_orders:
    feasible, itinerary, finish_time, total_travel = simulate_schedule(order)
    if feasible:
        feasible_schedules.append({
            "order": order,
            "itinerary": itinerary,
            "finish_time": finish_time,
            "total_travel": total_travel
        })

# Choose the best schedule.
# Our primary objective is to meet as many friends as possible (all 3).
# As a tie-breaker, we choose the schedule with the smallest finish time.
if feasible_schedules:
    best = min(feasible_schedules, key=lambda x: (x["finish_time"], x["total_travel"]))
    result = {"itinerary": best["itinerary"]}
else:
    result = {"itinerary": []}

# Output the result as JSON.
print(json.dumps(result))