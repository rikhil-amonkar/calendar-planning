#!/usr/bin/env python3
import itertools
import json

def time_to_minutes(t_str):
    # Expects format "H:MM" or "HH:MM" in 24-hour format.
    parts = t_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

# Travel times in minutes between locations.
# Keys: starting location; Values: dictionary mapping destination to travel time.
travel_times = {
    "Bayview": {
        "Pacific Heights": 23,
        "Mission District": 13,
        "Haight-Ashbury": 19,
        "Financial District": 19,
    },
    "Pacific Heights": {
        "Bayview": 22,
        "Mission District": 15,
        "Haight-Ashbury": 11,
        "Financial District": 13,
    },
    "Mission District": {
        "Bayview": 15,
        "Pacific Heights": 16,
        "Haight-Ashbury": 12,
        "Financial District": 17,
    },
    "Haight-Ashbury": {
        "Bayview": 18,
        "Pacific Heights": 12,
        "Mission District": 11,
        "Financial District": 21,
    },
    "Financial District": {
        "Bayview": 19,
        "Pacific Heights": 13,
        "Mission District": 17,
        "Haight-Ashbury": 19,
    }
}

# Friend meeting constraints.
# Each friend is represented as a dictionary with keys:
# name, location, avail_start, avail_end, duration (all times in minutes from midnight).
friends = [
    {
        "name": "Mary",
        "location": "Pacific Heights",
        "avail_start": time_to_minutes("10:00"),
        "avail_end": time_to_minutes("19:00"),
        "duration": 45
    },
    {
        "name": "Lisa",
        "location": "Mission District",
        "avail_start": time_to_minutes("20:30"),
        "avail_end": time_to_minutes("22:00"),
        "duration": 75
    },
    {
        "name": "Betty",
        "location": "Haight-Ashbury",
        "avail_start": time_to_minutes("7:15"),
        "avail_end": time_to_minutes("17:15"),
        "duration": 90
    },
    {
        "name": "Charles",
        "location": "Financial District",
        "avail_start": time_to_minutes("11:15"),
        "avail_end": time_to_minutes("15:00"),
        "duration": 120
    }
]

# Starting conditions: you arrive at Bayview at 9:00.
start_location = "Bayview"
start_time = time_to_minutes("9:00")

# We'll search for the schedule that meets the maximum number of friends.
# If there are schedules with the same maximum count, we choose the one with the earliest finishing time.
best_count = 0
best_finish = 10**9
best_itinerary = None

# We'll consider all possible subsets (permutations) of friends.
# This approach ensures that if not all meetings are feasible, we still pick the best.
n = len(friends)
for r in range(1, n+1):
    for perm in itertools.permutations(friends, r):
        # Simulate the schedule for this permutation.
        current_time = start_time
        current_location = start_location
        itinerary = []
        feasible = True
        # For each friend in the permutation, plan the meeting.
        for friend in perm:
            # Get travel time from current location to friend's meeting location.
            if current_location not in travel_times or friend["location"] not in travel_times[current_location]:
                feasible = False
                break
            travel = travel_times[current_location][friend["location"]]
            arrival_time = current_time + travel
            # Meeting cannot begin until the friend is available.
            meeting_start = max(arrival_time, friend["avail_start"])
            meeting_end = meeting_start + friend["duration"]
            # Check if the meeting can finish before the friend leaves.
            if meeting_end > friend["avail_end"]:
                feasible = False
                break
            # Record this meeting in the itinerary.
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
        if feasible:
            count = len(itinerary)
            finish_time = current_time
            # We want to maximize count and then minimize finish time.
            if count > best_count or (count == best_count and finish_time < best_finish):
                best_count = count
                best_finish = finish_time
                best_itinerary = itinerary

# Prepare the result JSON.
result = {"itinerary": best_itinerary if best_itinerary is not None else []}

# Output the result as a JSON-formatted dictionary.
print(json.dumps(result, indent=2))