"""
SOLUTION:
"""

import json
from itertools import combinations, permutations

# Helper functions for time
def to_minutes(h, m):
    return h * 60 + m

def minutes_to_str(total_minutes):
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h}:{m:02d}"

# Input variables: start location and time
start_location = "Pacific Heights"
start_time = to_minutes(9, 0)  # 9:00

# Travel times (in minutes), directional
travel = {
    "Pacific Heights": {
        "Nob Hill": 8,
        "Russian Hill": 7,
        "The Castro": 16,
        "Sunset District": 21,
        "Haight-Ashbury": 11,
    },
    "Nob Hill": {
        "Pacific Heights": 8,
        "Russian Hill": 5,
        "The Castro": 17,
        "Sunset District": 25,
        "Haight-Ashbury": 13,
    },
    "Russian Hill": {
        "Pacific Heights": 7,
        "Nob Hill": 5,
        "The Castro": 21,
        "Sunset District": 23,
        "Haight-Ashbury": 17,
    },
    "The Castro": {
        "Pacific Heights": 16,
        "Nob Hill": 16,
        "Russian Hill": 18,
        "Sunset District": 17,
        "Haight-Ashbury": 6,
    },
    "Sunset District": {
        "Pacific Heights": 21,
        "Nob Hill": 27,
        "Russian Hill": 24,
        "The Castro": 17,
        "Haight-Ashbury": 15,
    },
    "Haight-Ashbury": {
        "Pacific Heights": 12,
        "Nob Hill": 15,
        "Russian Hill": 17,
        "The Castro": 6,
        "Sunset District": 15,
    },
}

# Friends constraints
friends = {
    "Ronald": {
        "location": "Nob Hill",
        "start": to_minutes(10, 0),
        "end": to_minutes(17, 0),
        "min_duration": 105,
    },
    "Sarah": {
        "location": "Russian Hill",
        "start": to_minutes(7, 15),
        "end": to_minutes(9, 30),
        "min_duration": 45,
    },
    "Helen": {
        "location": "The Castro",
        "start": to_minutes(13, 30),
        "end": to_minutes(17, 0),
        "min_duration": 120,
    },
    "Joshua": {
        "location": "Sunset District",
        "start": to_minutes(14, 15),
        "end": to_minutes(19, 30),
        "min_duration": 90,
    },
    "Margaret": {
        "location": "Haight-Ashbury",
        "start": to_minutes(10, 15),
        "end": to_minutes(22, 0),
        "min_duration": 60,
    },
}

def try_schedule(order):
    curr_loc = start_location
    curr_time = start_time

    itinerary = []
    total_wait = 0
    total_travel = 0
    total_meeting = 0

    last_idx = None
    prev_friend = None  # dict of previous friend's constraints

    for name in order:
        f = friends[name]
        # Ensure travel time exists
        if curr_loc not in travel or f["location"] not in travel[curr_loc]:
            return None  # missing travel data
        ttime = travel[curr_loc][f["location"]]

        arrival_if_leave_now = curr_time + ttime

        if arrival_if_leave_now <= f["start"]:
            # We can align arrival to the friend's start by delaying departure.
            target_depart = f["start"] - ttime

            if prev_friend is not None:
                # Try to extend previous meeting to reduce waiting
                max_extend = max(0, prev_friend["end"] - curr_time)
                desired_extend = max(0, target_depart - curr_time)
                extension = min(max_extend, desired_extend)
                if extension > 0 and last_idx is not None:
                    # Extend the previous meeting's end time
                    itinerary[last_idx]["end_min"] += extension
                    curr_time += extension
                    total_meeting += extension

                # Any remaining gap is waiting (idle) before departure
                depart_time = max(curr_time, target_depart)
                if depart_time > curr_time:
                    total_wait += depart_time - curr_time
                    curr_time = depart_time
            else:
                # At the start of the day, wait at base to align arrival
                depart_time = max(curr_time, target_depart)
                if depart_time > curr_time:
                    total_wait += depart_time - curr_time
                    curr_time = depart_time
        else:
            # We're already later than the friend's start; depart immediately
            depart_time = curr_time

        # Travel
        curr_time += ttime
        total_travel += ttime

        # If still early after travel (shouldn't typically happen), wait at location
        if curr_time < f["start"]:
            total_wait += f["start"] - curr_time
            curr_time = f["start"]

        # Meeting
        meet_start = curr_time
        meet_end = meet_start + f["min_duration"]
        if meet_end > f["end"]:
            return None  # cannot fit minimum meeting duration within availability

        itinerary.append({
            "action": "meet",
            "location": f["location"],
            "person": name,
            "start_min": meet_start,
            "end_min": meet_end
        })
        last_idx = len(itinerary) - 1
        total_meeting += f["min_duration"]

        # Update state
        curr_time = meet_end
        curr_loc = f["location"]
        prev_friend = f

    finish_time = curr_time

    return {
        "itinerary_raw": itinerary,
        "metrics": {
            "count": len(order),
            "total_wait": total_wait,
            "finish_time": finish_time,
            "total_travel": total_travel,
            "total_meeting": total_meeting,
        }
    }

def better_metrics(a, b):
    """
    Return True if metrics 'a' is better than 'b' by our optimization goals:
    - Maximize number of friends met
    - Minimize total waiting time
    - Minimize finish time (makespan)
    - Minimize total travel time
    - Maximize total meeting time
    """
    keys = ["count", "total_wait", "finish_time", "total_travel", "total_meeting"]
    # Note: 'count' and 'total_meeting' maximize; others minimize
    if a is None:
        return False
    if b is None:
        return True

    if a["count"] != b["count"]:
        return a["count"] > b["count"]
    if a["total_wait"] != b["total_wait"]:
        return a["total_wait"] < b["total_wait"]
    if a["finish_time"] != b["finish_time"]:
        return a["finish_time"] < b["finish_time"]
    if a["total_travel"] != b["total_travel"]:
        return a["total_travel"] < b["total_travel"]
    if a["total_meeting"] != b["total_meeting"]:
        return a["total_meeting"] > b["total_meeting"]
    return False

# Search for optimal schedule:
names = list(friends.keys())
best_plan = None
best_metrics = None

# Try subsets in descending order of size (max people met)
for size in range(len(names), 0, -1):
    best_for_size = None
    best_metrics_for_size = None
    for subset in combinations(names, size):
        for order in permutations(subset):
            attempt = try_schedule(order)
            if attempt is None:
                continue
            metrics = attempt["metrics"]
            if best_metrics_for_size is None or better_metrics(metrics, best_metrics_for_size):
                best_for_size = attempt
                best_metrics_for_size = metrics
    if best_for_size is not None:
        best_plan = best_for_size
        best_metrics = best_metrics_for_size
        break  # Found the best schedule with maximum number of meetings

# Convert itinerary to required JSON format
output = {"itinerary": []}

if best_plan:
    for ev in best_plan["itinerary_raw"]:
        output["itinerary"].append({
            "action": ev["action"],
            "location": ev["location"],
            "person": ev["person"],
            "start_time": minutes_to_str(ev["start_min"]),
            "end_time": minutes_to_str(ev["end_min"]),
        })

print(json.dumps(output, indent=2))