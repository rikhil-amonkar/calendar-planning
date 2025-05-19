#!/usr/bin/env python3
import json
import itertools

# Helper functions to convert time between "H:MM" and minutes since midnight
def time_to_minutes(t):
    # Expected t format "H:MM" or "HH:MM"
    parts = t.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(m):
    # returns time in "H:MM" where hour is not zero padded and minutes are two digits.
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

# Define travel times as dictionary with (from, to) keys (in minutes)
travel_times = {
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Richmond District"): 18
}

# Define friend meeting constraints data.
friends = {
    "Betty": {
        "location": "Presidio",
        "avail_start": time_to_minutes("10:15"),
        "avail_end": time_to_minutes("21:30"),
        "min_duration": 45
    },
    "David": {
        "location": "Richmond District",
        "avail_start": time_to_minutes("13:00"),
        "avail_end": time_to_minutes("20:15"),
        "min_duration": 90
    },
    "Barbara": {
        "location": "Fisherman's Wharf",
        "avail_start": time_to_minutes("9:15"),
        "avail_end": time_to_minutes("20:15"),
        "min_duration": 120
    }
}

# Starting point info
start_location = "Embarcadero"
start_time = time_to_minutes("9:00")

# Function to compute schedule for a given order of meetings.
def compute_schedule(order):
    itinerary = []
    current_location = start_location
    current_time = start_time
    total_idle = 0  # total waiting time
    for person in order:
        friend = friends[person]
        dest = friend["location"]
        # Get travel time from current location to destination
        travel = travel_times.get((current_location, dest), None)
        if travel is None:
            # If travel time not defined, schedule is not feasible.
            return None, None
        # Arrive at destination
        arrival_time = current_time + travel
        # Meeting can only start when friend is available.
        meeting_start = max(arrival_time, friend["avail_start"])
        # Calculate waiting time if any.
        waiting = meeting_start - arrival_time
        total_idle += waiting
        meeting_end = meeting_start + friend["min_duration"]
        # Check if meeting finishes before friend leaves
        if meeting_end > friend["avail_end"]:
            return None, None  # not feasible
        # Record itinerary step
        itinerary.append({
            "action": "meet",
            "location": dest,
            "person": person,
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        # update current_time and current_location
        current_time = meeting_end
        current_location = dest
    return itinerary, current_time

# Try every permutation of friend meeting order and choose the one that is feasible and minimizes finishing time (and waiting time)
best_itinerary = None
best_finish_time = None
best_idle = None
for order in itertools.permutations(friends.keys()):
    itinerary, finish_time = compute_schedule(order)
    if itinerary is None:
        continue
    # Also compute total waiting time in this itinerary
    # (We already computed waiting inside compute_schedule using total_idle but not returned.
    # To recalc waiting, simulate once more.)
    total_wait = 0
    current_location = start_location
    current_time = start_time
    for person in order:
        friend = friends[person]
        dest = friend["location"]
        travel = travel_times[(current_location, dest)]
        arrival_time = current_time + travel
        meeting_start = max(arrival_time, friend["avail_start"])
        total_wait += meeting_start - arrival_time
        meeting_end = meeting_start + friend["min_duration"]
        current_time = meeting_end
        current_location = dest

    # Use finish time as primary measure and waiting as secondary.
    if best_finish_time is None or finish_time < best_finish_time or (finish_time == best_finish_time and total_wait < best_idle):
        best_finish_time = finish_time
        best_itinerary = itinerary
        best_idle = total_wait

# If no itinerary is feasible, return a message in JSON.
if best_itinerary is None:
    output = {"error": "No feasible meeting schedule found."}
else:
    output = {"itinerary": best_itinerary}

# Output the result as JSON.
print(json.dumps(output, indent=2))