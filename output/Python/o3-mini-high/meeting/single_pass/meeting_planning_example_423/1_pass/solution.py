#!/usr/bin/env python3
import itertools
import json

def minutes_to_str(minutes):
    hrs = minutes // 60
    mins = minutes % 60
    return f"{hrs}:{mins:02d}"

# Define travel times in minutes between locations
travel_times = {
    "Presidio": {
        "Richmond District": 7,
        "North Beach": 18,
        "Financial District": 23,
        "Golden Gate Park": 12,
        "Union Square": 22
    },
    "Richmond District": {
        "Presidio": 7,
        "North Beach": 17,
        "Financial District": 22,
        "Golden Gate Park": 9,
        "Union Square": 21
    },
    "North Beach": {
        "Presidio": 17,
        "Richmond District": 18,
        "Financial District": 8,
        "Golden Gate Park": 22,
        "Union Square": 7
    },
    "Financial District": {
        "Presidio": 22,
        "Richmond District": 21,
        "North Beach": 7,
        "Golden Gate Park": 23,
        "Union Square": 9
    },
    "Golden Gate Park": {
        "Presidio": 11,
        "Richmond District": 7,
        "North Beach": 24,
        "Financial District": 26,
        "Union Square": 22
    },
    "Union Square": {
        "Presidio": 24,
        "Richmond District": 20,
        "North Beach": 10,
        "Financial District": 9,
        "Golden Gate Park": 22
    }
}

# Define the friends' meeting constraints.
# Times are in minutes after midnight.
friends = [
    {
        "name": "Jason",
        "location": "Richmond District",
        "avail_start": 13 * 60,         # 13:00 = 780
        "avail_end": 20 * 60 + 45,        # 20:45 = 1245
        "duration": 90
    },
    {
        "name": "Melissa",
        "location": "North Beach",
        "avail_start": 18 * 60 + 45,      # 18:45 = 1125
        "avail_end": 20 * 60 + 15,        # 20:15 = 1215
        "duration": 45
    },
    {
        "name": "Brian",
        "location": "Financial District",
        "avail_start": 9 * 60 + 45,       # 9:45 = 585
        "avail_end": 21 * 60 + 45,        # 21:45 = 1305
        "duration": 15
    },
    {
        "name": "Elizabeth",
        "location": "Golden Gate Park",
        "avail_start": 8 * 60 + 45,       # 8:45 = 525
        "avail_end": 21 * 60 + 30,        # 21:30 = 1290
        "duration": 105
    },
    {
        "name": "Laura",
        "location": "Union Square",
        "avail_start": 14 * 60 + 15,      # 14:15 = 855
        "avail_end": 19 * 60 + 30,        # 19:30 = 1170
        "duration": 75
    }
]

# Simulation function:
# Given an ordering (tuple of friend dicts), simulate the schedule 
# starting from Presidio at 9:00 (540 minutes) and check if each meeting fits
def simulate_schedule(order):
    current_time = 9 * 60  # 9:00 AM => 540 minutes
    current_location = "Presidio"
    itinerary = []
    total_wait = 0

    for friend in order:
        # Calculate travel time from current location to friend's location.
        travel = travel_times[current_location][friend["location"]]
        arrival_time = current_time + travel
        # Wait until friend's available start time if arriving early.
        meeting_start = max(arrival_time, friend["avail_start"])
        wait = meeting_start - arrival_time
        meeting_end = meeting_start + friend["duration"]
        # Check if meeting can be completed within the friend's available window.
        if meeting_end > friend["avail_end"]:
            return None  # This order is not feasible.
        # Append this meeting event to itinerary.
        event = {
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": minutes_to_str(meeting_start),
            "end_time": minutes_to_str(meeting_end)
        }
        itinerary.append(event)
        total_wait += wait
        current_time = meeting_end
        current_location = friend["location"]
    return (itinerary, current_time, total_wait)

def main():
    best_itinerary = None
    best_finish = None
    max_count = 0

    n = len(friends)
    # Check for schedules with maximum possible meetings.
    # We iterate over all combinations (subsets) of friends and then all permutations.
    for k in range(n, 0, -1):
        candidate_schedules = []
        for combo in itertools.combinations(friends, k):
            for perm in itertools.permutations(combo):
                result = simulate_schedule(perm)
                if result is not None:
                    itinerary, finish_time, total_wait = result
                    candidate_schedules.append((itinerary, finish_time, total_wait))
        if candidate_schedules:
            # We found at least one feasible schedule meeting k friends.
            # Choose the one with earliest finish time as a tiebreaker.
            candidate_schedules.sort(key=lambda x: (x[1], x[2]))
            best_itinerary = candidate_schedules[0][0]
            max_count = k
            break

    output = {"itinerary": best_itinerary if best_itinerary is not None else []}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()