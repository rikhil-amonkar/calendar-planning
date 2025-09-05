#!/usr/bin/env python3
import json
import itertools

# Helper function: converts minutes since midnight to "H:MM" (24-hour) string.
def minutes_to_time_str(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Define the travel times (in minutes) between locations.
# Keys are origin locations and values are dictionaries mapping destination to travel time.
travel_times = {
    "The Castro": {"Alamo Square": 8, "Union Square": 19, "Chinatown": 20},
    "Alamo Square": {"The Castro": 8, "Union Square": 14, "Chinatown": 16},
    "Union Square": {"The Castro": 19, "Alamo Square": 15, "Chinatown": 7},
    "Chinatown": {"The Castro": 22, "Alamo Square": 17, "Union Square": 7}
}

# Define friend meeting constraints.
# Times are in minutes since midnight.
# 9:00 AM is 540 minutes.
# For Emily: available 11:45 (705) to 15:15 (915) with min duration 105 minutes.
# For Barbara: available 16:45 (1005) to 18:15 (1095) with min duration 60 minutes.
# For William: available 17:15 (1035) to 19:00 (1140) with min duration 105 minutes.
friends = [
    {
        "name": "Emily",
        "location": "Alamo Square",
        "avail_start": 11 * 60 + 45,  # 11:45 AM -> 705
        "avail_end": 15 * 60 + 15,    # 15:15 -> 915
        "min_duration": 105
    },
    {
        "name": "Barbara",
        "location": "Union Square",
        "avail_start": 16 * 60 + 45,  # 16:45 -> 1005
        "avail_end": 18 * 60 + 15,    # 18:15 -> 1095
        "min_duration": 60
    },
    {
        "name": "William",
        "location": "Chinatown",
        "avail_start": 17 * 60 + 15,  # 17:15 -> 1035
        "avail_end": 19 * 60,         # 19:00 -> 1140
        "min_duration": 105
    }
]

# The schedule always starts at "The Castro" at 9:00 AM (540 minutes).
START_LOCATION = "The Castro"
START_TIME = 9 * 60  # 9:00 AM -> 540 minutes

# We will consider all possible subsets (and orders) of the friends list.
# For each ordering, we simulate the day and check if the meeting can be scheduled.
def simulate_schedule(order):
    itinerary = []
    current_time = START_TIME
    current_location = START_LOCATION

    # For each friend in the order, compute travel and waiting times.
    for friend in order:
        # Get travel time from current location to friend's location.
        travel_time = travel_times[current_location][friend["location"]]
        arrival_time = current_time + travel_time
        # Meeting cannot start before the friend is available.
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["min_duration"]
        # Check if the meeting would finish before the friend leaves.
        if meeting_end > friend["avail_end"]:
            return None  # This order is not feasible.
        
        # Record the meeting event.
        event = {
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": minutes_to_time_str(meeting_start),
            "end_time": minutes_to_time_str(meeting_end)
        }
        itinerary.append(event)
        # Update current time and location.
        current_time = meeting_end
        current_location = friend["location"]
    
    return {
        "itinerary": itinerary,
        "friend_count": len(order),
        "finish_time": current_time
    }

# Try all subsets (of size 1 to 3) and all orderings, and pick the best schedule.
all_possible_schedules = []

# Consider non-empty subsets of friends
for r in range(1, len(friends) + 1):
    for subset in itertools.combinations(friends, r):
        # For each subset, try every permutation (order)
        for order in itertools.permutations(subset):
            result = simulate_schedule(order)
            if result is not None:
                all_possible_schedules.append(result)

# Optimization criteria:
# 1. Maximize number of meetings (friend_count)
# 2. In case of tie, choose the schedule that finishes earliest.
best_schedule = None
for schedule in all_possible_schedules:
    if best_schedule is None:
        best_schedule = schedule
    else:
        if schedule["friend_count"] > best_schedule["friend_count"]:
            best_schedule = schedule
        elif schedule["friend_count"] == best_schedule["friend_count"]:
            if schedule["finish_time"] < best_schedule["finish_time"]:
                best_schedule = schedule

# If no schedule is found (should not happen), output an empty itinerary.
if best_schedule is None:
    output = {"itinerary": []}
else:
    output = {"itinerary": best_schedule["itinerary"]}

# Print the output as JSON-formatted dictionary.
print(json.dumps(output, indent=2))