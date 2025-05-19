#!/usr/bin/env python3
import json
import itertools

# Define helper functions to convert times to minutes from midnight and back.
def time_to_minutes(t):
    # t in "H:MM" format, e.g., "9:00" or "16:45"
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

# Define travel times (in minutes) in a dictionary with keys (from, to)
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
    ("Russian Hill", "Presidio"): 14,
}

# Define friends meeting constraints as dictionaries.
# Each friend dict will include: name, location, available start, available end, and minimum meeting duration.
friends = [
    {
        "name": "Timothy",
        "location": "Alamo Square",
        "avail_start": time_to_minutes("12:00"),
        "avail_end": time_to_minutes("16:15"),
        "min_duration": 105
    },
    {
        "name": "Mark",
        "location": "Presidio",
        "avail_start": time_to_minutes("18:45"),
        "avail_end": time_to_minutes("21:00"),
        "min_duration": 60
    },
    {
        "name": "Joseph",
        "location": "Russian Hill",
        "avail_start": time_to_minutes("16:45"),
        "avail_end": time_to_minutes("21:30"),
        "min_duration": 60
    }
]

# Starting parameters
start_location = "Golden Gate Park"
start_time = time_to_minutes("9:00")

# Function to simulate a given order and compute schedule if possible.
def simulate_schedule(order):
    itinerary = []
    current_time = start_time
    current_location = start_location
    
    for friend in order:
        # Compute travel time from current location to friend's location
        if current_location == friend["location"]:
            travel_time = 0
        else:
            travel_time = travel_times.get((current_location, friend["location"]), None)
            if travel_time is None:
                # If travel time is not defined, invalid route.
                return None
        arrival_time = current_time + travel_time
        # Meeting can only start once friend is available.
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["min_duration"]
        # Check if meeting ends before friend leaves.
        if meeting_end > friend["avail_end"]:
            return None  # invalid schedule
        # Record meeting in itinerary.
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        # Update current time and location.
        current_time = meeting_end
        current_location = friend["location"]
    return (itinerary, current_time)

# Evaluate all permutations to pick the optimal schedule.
best_schedule = None
best_finish = None

for order in itertools.permutations(friends):
    result = simulate_schedule(order)
    if result is not None:
        itinerary, finish_time = result
        # We want to maximize number of meetings. All valid schedules here meet all three.
        # To pick an optimal one, pick the one that finishes earliest.
        if best_finish is None or finish_time < best_finish:
            best_finish = finish_time
            best_schedule = itinerary

# Prepare the JSON output dictionary
output = {
    "itinerary": best_schedule if best_schedule is not None else []
}

# Output the result as JSON
print(json.dumps(output, indent=2))
                
if __name__ == '__main__':
    pass