#!/usr/bin/env python3
import json
import itertools

def time_to_minutes(time_str):
    # Convert a time string "H:MM" into minutes past midnight.
    hours, minutes = time_str.split(":")
    return int(hours) * 60 + int(minutes)

def minutes_to_time(minutes):
    # Convert minutes past midnight into a time string "H:MM" (24-hour format, no leading zero for hour)
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Define travel times between locations (in minutes)
travel_times = {
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Mission District"): 15,
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Mission District"): 18,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Mission District"): 17,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Mission District"): 10,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Financial District"): 17,
    ("Mission District", "Alamo Square"): 11
}

# Define friend meeting constraints as a list of dictionaries.
# Times are stored as minutes past midnight.
friends = [
    {
        "name": "Helen",
        "location": "North Beach",
        "avail_start": time_to_minutes("9:00"),
        "avail_end": time_to_minutes("17:00"),
        "duration": 15
    },
    {
        "name": "Betty",
        "location": "Financial District",
        "avail_start": time_to_minutes("19:00"),
        "avail_end": time_to_minutes("21:45"),
        "duration": 90
    },
    {
        "name": "Amanda",
        "location": "Alamo Square",
        "avail_start": time_to_minutes("19:45"),
        "avail_end": time_to_minutes("21:00"),
        "duration": 60
    },
    {
        "name": "Kevin",
        "location": "Mission District",
        "avail_start": time_to_minutes("10:45"),
        "avail_end": time_to_minutes("14:45"),
        "duration": 45
    }
]

# Starting parameters
start_location = "Pacific Heights"
start_time = time_to_minutes("9:00")

def compute_schedule(order):
    """
    Given an ordered tuple of friend dictionaries, try to compute a schedule.
    Returns a list of meeting actions if feasible, otherwise returns None.
    Each meeting is scheduled at the earliest possible time (waiting if needed).
    """
    itinerary = []
    current_time = start_time
    current_location = start_location

    for friend in order:
        # Check travel time from current location to friend's meeting location
        key = (current_location, friend["location"])
        if key not in travel_times:
            return None  # if travel time not defined, schedule fails.
        travel = travel_times[key]
        arrival_time = current_time + travel
        # Meeting cannot start before friend becomes available.
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["duration"]
        # Check if meeting ends before friend's availability window closes.
        if meeting_end > friend["avail_end"]:
            return None
        # Add meeting action to itinerary.
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        current_time = meeting_end
        current_location = friend["location"]

    return itinerary

# Try all possible subsets and orders of friend meetings to maximize the count.
best_itinerary = None
best_count = 0
best_finish_time = None

# Iterate over all non-empty subsets of friends.
n = len(friends)
for r in range(1, n+1):
    for subset in itertools.combinations(friends, r):
        for order in itertools.permutations(subset):
            sched = compute_schedule(order)
            if sched is not None:
                # Number of meetings scheduled in this order.
                count = r
                # Compute finish time by simulating through the order.
                current_time = start_time
                current_location = start_location
                feasible = True
                for friend in order:
                    travel = travel_times[(current_location, friend["location"])]
                    arrival = current_time + travel
                    start_meet = max(arrival, friend["avail_start"])
                    end_meet = start_meet + friend["duration"]
                    if end_meet > friend["avail_end"]:
                        feasible = False
                        break
                    current_time = end_meet
                    current_location = friend["location"]
                if not feasible:
                    continue
                finish_time = current_time

                # Update best schedule if this one meets more friends, or if equal count and finishes earlier.
                if count > best_count or (count == best_count and (best_finish_time is None or finish_time < best_finish_time)):
                    best_itinerary = sched
                    best_count = count
                    best_finish_time = finish_time

# Prepare the final result as a JSON formatted dictionary.
result = {
    "itinerary": best_itinerary if best_itinerary is not None else []
}

print(json.dumps(result, indent=2))