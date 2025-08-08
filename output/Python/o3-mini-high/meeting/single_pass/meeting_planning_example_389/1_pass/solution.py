#!/usr/bin/env python3
import json
import itertools

def time_to_minutes(t):
    # Convert a time string "H:MM" (24-hour) to minutes since midnight.
    parts = t.split(":")
    hour = int(parts[0])
    minute = int(parts[1])
    return hour * 60 + minute

def minutes_to_time(m):
    # Convert minutes since midnight into a time string "H:MM" (24-hour, no leading zero for hour)
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

# Travel times in minutes between locations.
travel_times = {
    "Haight-Ashbury": {
        "Fisherman's Wharf": 23,
        "Richmond District": 10,
        "Mission District": 11,
        "Bayview": 18
    },
    "Fisherman's Wharf": {
        "Haight-Ashbury": 22,
        "Richmond District": 18,
        "Mission District": 22,
        "Bayview": 26
    },
    "Richmond District": {
        "Haight-Ashbury": 10,
        "Fisherman's Wharf": 18,
        "Mission District": 20,
        "Bayview": 26
    },
    "Mission District": {
        "Haight-Ashbury": 12,
        "Fisherman's Wharf": 22,
        "Richmond District": 20,
        "Bayview": 15
    },
    "Bayview": {
        "Haight-Ashbury": 19,
        "Fisherman's Wharf": 25,
        "Richmond District": 25,
        "Mission District": 13
    }
}

# Friend meeting constraints.
friends = {
    "Sarah": {
        "location": "Fisherman's Wharf",
        "avail_start": time_to_minutes("14:45"),
        "avail_end": time_to_minutes("17:30"),
        "min_duration": 105
    },
    "Mary": {
        "location": "Richmond District",
        "avail_start": time_to_minutes("13:00"),
        "avail_end": time_to_minutes("19:15"),
        "min_duration": 75
    },
    "Helen": {
        "location": "Mission District",
        "avail_start": time_to_minutes("21:45"),
        "avail_end": time_to_minutes("22:30"),
        "min_duration": 30
    },
    "Thomas": {
        "location": "Bayview",
        "avail_start": time_to_minutes("15:15"),
        "avail_end": time_to_minutes("18:45"),
        "min_duration": 120
    }
}

# Starting conditions.
start_location = "Haight-Ashbury"
start_time = time_to_minutes("9:00")

# We want to maximize the number of friends met.
best_schedule = None
best_count = 0
best_finish_time = None
all_friend_names = list(friends.keys())

# Try all possible subsets (and orders) of friends.
# Since there are only 4 friends, we consider all non-empty combinations.
for r in range(len(all_friend_names), 0, -1):
    for subset in itertools.combinations(all_friend_names, r):
        for order in itertools.permutations(subset):
            current_time = start_time
            current_location = start_location
            itinerary = []
            feasible = True
            for friend in order:
                friend_info = friends[friend]
                destination = friend_info["location"]
                travel = travel_times[current_location][destination]
                arrival_time = current_time + travel
                # Wait if arrived before the friend's available start time.
                meeting_start = max(arrival_time, friend_info["avail_start"])
                meeting_end = meeting_start + friend_info["min_duration"]
                # Check if meeting can finish before the friend leaves.
                if meeting_end > friend_info["avail_end"]:
                    feasible = False
                    break
                itinerary.append({
                    "action": "meet",
                    "location": destination,
                    "person": friend,
                    "start_time": minutes_to_time(meeting_start),
                    "end_time": minutes_to_time(meeting_end)
                })
                current_time = meeting_end
                current_location = destination
            if feasible:
                # We have a schedule that meets r friends.
                if r > best_count or (r == best_count and (best_finish_time is None or current_time < best_finish_time)):
                    best_count = r
                    best_finish_time = current_time
                    best_schedule = itinerary
    if best_schedule is not None and best_count == r:
        # Found an optimal schedule with maximum number of friends for this subset size.
        break

if best_schedule is None:
    best_schedule = []

result = {"itinerary": best_schedule}
print(json.dumps(result))