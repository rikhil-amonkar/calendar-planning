#!/usr/bin/env python3
import json
import itertools

# Helper functions to convert time formats
def time_to_minutes(time_str):
    # time_str expected as "H:MM" (e.g., "9:00" or "12:00")
    parts = time_str.split(":")
    hour = int(parts[0])
    minute = int(parts[1])
    return hour * 60 + minute

def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Travel times in minutes between locations as provided.
# (origin, destination): travel_time
travel_times = {
    ("Golden Gate Park", "Alamo Square"): 10,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Presidio"): 18,
    ("Alamo Square", "Russian Hill"): 13,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Alamo Square"): 18,
    ("Presidio", "Russian Hill"): 14,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Presidio"): 14
}

# Meeting data for each friend, with constraints.
# The available start/end times are stored in minutes and meeting durations in minutes.
friends = [
    {
        "person": "Timothy",
        "location": "Alamo Square",
        "avail_start": time_to_minutes("12:00"),
        "avail_end": time_to_minutes("16:15"),
        "min_duration": 105
    },
    {
        "person": "Mark",
        "location": "Presidio",
        "avail_start": time_to_minutes("18:45"),
        "avail_end": time_to_minutes("21:00"),
        "min_duration": 60
    },
    {
        "person": "Joseph",
        "location": "Russian Hill",
        "avail_start": time_to_minutes("16:45"),
        "avail_end": time_to_minutes("21:30"),
        "min_duration": 60
    }
]

# Starting point and time
start_location = "Golden Gate Park"
start_time = time_to_minutes("9:00")

def simulate_schedule(order):
    current_time = start_time
    current_location = start_location
    itinerary = []
    for friend in order:
        # Calculate travel time from current location to meeting location
        key = (current_location, friend["location"])
        if key not in travel_times:
            # If for some reason no travel time is defined, mark schedule as invalid.
            return None, None
        travel = travel_times[key]
        arrival_time = current_time + travel
        # Wait until friend is available if arrived earlier.
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["min_duration"]
        # Check if meeting can finish before the friend leaves.
        if meeting_end > friend["avail_end"]:
            return None, None  # Schedule invalid for this order
        # Record the meeting in the itinerary.
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["person"],
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        # Update current time and location after meeting.
        current_time = meeting_end
        current_location = friend["location"]
    return itinerary, current_time

# Evaluate all permutations of meetings to find the schedule that meets all constraints
# and has the earliest finishing time.
best_schedule = None
best_finish_time = float("inf")

for order in itertools.permutations(friends):
    schedule, finish_time = simulate_schedule(order)
    if schedule is not None:
        # Optimize by choosing schedule that finishes earliest.
        if finish_time < best_finish_time:
            best_finish_time = finish_time
            best_schedule = schedule

result = {"itinerary": best_schedule if best_schedule is not None else []}

if __name__ == "__main__":
    print(json.dumps(result))