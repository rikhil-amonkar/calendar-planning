#!/usr/bin/env python3
import itertools
import json

# Helper functions to convert time formats.
def time_to_minutes(t_str):
    # expects format "H:MM" or "HH:MM" in 24-hour time
    parts = t_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    return hour * 60 + minute

def minutes_to_time(m):
    hour = m // 60
    minute = m % 60
    # Format minutes with two digits, hour without a leading zero.
    return f"{hour}:{minute:02d}"

# Travel times between locations (in minutes)
travel_times = {
    "Pacific Heights": {
        "North Beach": 9,
        "Financial District": 13,
        "Alamo Square": 10,
        "Mission District": 15
    },
    "North Beach": {
        "Pacific Heights": 8,
        "Financial District": 8,
        "Alamo Square": 16,
        "Mission District": 18
    },
    "Financial District": {
        "Pacific Heights": 13,
        "North Beach": 7,
        "Alamo Square": 17,
        "Mission District": 17
    },
    "Alamo Square": {
        "Pacific Heights": 10,
        "North Beach": 15,
        "Financial District": 17,
        "Mission District": 10
    },
    "Mission District": {
        "Pacific Heights": 16,
        "North Beach": 17,
        "Financial District": 17,
        "Alamo Square": 11
    }
}

# Meeting constraints for each friend.
# Each meeting is defined by: person, location, available_start, available_end, and minimum meeting duration (in minutes)
# Times are in 24-hour format.
meetings = [
    {
        "person": "Helen",
        "location": "North Beach",
        "avail_start": time_to_minutes("9:00"),
        "avail_end": time_to_minutes("17:00"),
        "min_duration": 15
    },
    {
        "person": "Betty",
        "location": "Financial District",
        "avail_start": time_to_minutes("19:00"),
        "avail_end": time_to_minutes("21:45"),
        "min_duration": 90
    },
    {
        "person": "Amanda",
        "location": "Alamo Square",
        "avail_start": time_to_minutes("19:45"),
        "avail_end": time_to_minutes("21:00"),
        "min_duration": 60
    },
    {
        "person": "Kevin",
        "location": "Mission District",
        "avail_start": time_to_minutes("10:45"),
        "avail_end": time_to_minutes("14:45"),
        "min_duration": 45
    }
]

# Starting conditions
start_location = "Pacific Heights"
start_time = time_to_minutes("9:00")

# The goal is to maximize number of friends met subject to constraints.
# We will generate all possible subsets (i.e. combinations) and orders (permutations)
# and then choose the itinerary that meets all timing constraints,
# and among feasible ones, choose the one with maximum count and then maximum total meeting time.
best_itinerary = None
best_count = 0
best_total_meeting = 0

# We'll consider subsets of meetings from the full list.
n = len(meetings)
# Iterate over all non-empty subsets
for r in range(n, 0, -1):
    for subset in itertools.combinations(meetings, r):
        # Check all orderings (permutations) of this subset.
        for perm in itertools.permutations(subset):
            current_time = start_time
            current_location = start_location
            itinerary = []
            valid = True
            total_meeting_time = 0
            # Process each meeting in the permutation order.
            for meet in perm:
                # Travel to friend's location
                travel = travel_times[current_location][meet["location"]]
                arrival_time = current_time + travel
                # The meeting can only start when both you have arrived and the friend is available.
                meeting_start = max(arrival_time, meet["avail_start"])
                meeting_end = meeting_start + meet["min_duration"]
                # Check if the meeting fits within the friend's available window.
                if meeting_end > meet["avail_end"]:
                    valid = False
                    break
                # Append the meeting event to our itinerary.
                itinerary.append({
                    "action": "meet",
                    "location": meet["location"],
                    "person": meet["person"],
                    "start_time": minutes_to_time(meeting_start),
                    "end_time": minutes_to_time(meeting_end)
                })
                total_meeting_time += meet["min_duration"]
                # Update current time and location
                current_time = meeting_end
                current_location = meet["location"]
            # If itinerary is valid and meets more friends, update best candidate.
            if valid:
                meeting_count = len(itinerary)
                # Primary goal: maximize number of friends met.
                if meeting_count > best_count or (meeting_count == best_count and total_meeting_time > best_total_meeting):
                    best_count = meeting_count
                    best_total_meeting = total_meeting_time
                    best_itinerary = itinerary
    # If we found any valid itinerary with r meetings, we don't need to try lower r.
    if best_itinerary is not None and len(best_itinerary) == r:
        break

# Prepare the result in the required JSON format.
result = {
    "itinerary": best_itinerary if best_itinerary is not None else []
}

# Output the JSON result.
print(json.dumps(result, indent=2))