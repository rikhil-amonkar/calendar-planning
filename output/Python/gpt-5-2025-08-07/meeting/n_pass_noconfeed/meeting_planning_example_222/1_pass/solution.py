"""
SOLUTION:
"""

import json
from itertools import combinations, permutations

# -----------------------------
# Helper functions for time
# -----------------------------
def to_minutes(h, m):
    return h * 60 + m

def parse_time_str(tstr):
    # 'H:MM' expected
    h, m = tstr.split(":")
    return int(h) * 60 + int(m)

def time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# -----------------------------
# Input parameters
# -----------------------------
locations = ["Nob Hill", "North Beach", "Fisherman's Wharf", "Bayview"]

travel = {
    "Nob Hill": {
        "North Beach": 8,
        "Fisherman's Wharf": 11,
        "Bayview": 19
    },
    "North Beach": {
        "Nob Hill": 7,
        "Fisherman's Wharf": 5,
        "Bayview": 22
    },
    "Fisherman's Wharf": {
        "Nob Hill": 11,
        "North Beach": 6,
        "Bayview": 26
    },
    "Bayview": {
        "Nob Hill": 20,
        "North Beach": 21,
        "Fisherman's Wharf": 25
    }
}

def get_travel_time(src, dst):
    if src == dst:
        return 0
    return travel[src][dst]

# Constraints
start_location = "Nob Hill"
start_time = parse_time_str("9:00")

people = {
    "Helen": {
        "location": "North Beach",
        "avail_start": parse_time_str("7:00"),
        "avail_end": parse_time_str("16:45"),
        "min_duration": 120
    },
    "Kimberly": {
        "location": "Fisherman's Wharf",
        "avail_start": parse_time_str("16:30"),
        "avail_end": parse_time_str("21:00"),
        "min_duration": 45
    },
    "Patricia": {
        "location": "Bayview",
        "avail_start": parse_time_str("18:00"),
        "avail_end": parse_time_str("21:15"),
        "min_duration": 120
    }
}

# -----------------------------
# Scheduling logic
# -----------------------------
def compute_schedule_for_order(order_names):
    itinerary = []
    current_loc = start_location
    current_time = start_time
    total_travel = 0

    order = [ (name, people[name]) for name in order_names ]

    for i, (name, p) in enumerate(order):
        # Travel to this person's location
        t_travel = get_travel_time(current_loc, p["location"])
        arrive = current_time + t_travel
        total_travel += t_travel

        # Compute meeting start
        start_meet = max(arrive, p["avail_start"])

        # Check if we can fit minimum duration
        if start_meet + p["min_duration"] > p["avail_end"]:
            return None  # infeasible

        # Determine end time
        if i < len(order) - 1:
            next_name, nxt = order[i+1]
            t_to_next = get_travel_time(p["location"], nxt["location"])
            latest_leave_for_next = nxt["avail_end"] - nxt["min_duration"] - t_to_next
            allowed_latest_departure = min(p["avail_end"], latest_leave_for_next)
            min_end = start_meet + p["min_duration"]
            if allowed_latest_departure < min_end:
                return None  # cannot satisfy both current min and next min
            end_meet = allowed_latest_departure
        else:
            # Last person: extend to their availability end
            end_meet = p["avail_end"]

        itinerary.append({
            "action": "meet",
            "location": p["location"],
            "person": name,
            "start_time": time_str(start_meet),
            "end_time": time_str(end_meet)
        })

        current_loc = p["location"]
        current_time = end_meet

    # Validate downstream feasibility explicitly (already done during construction, but ensure correctness)
    # Also compute scoring metrics
    total_meeting_minutes = 0
    for item in itinerary:
        s = parse_time_str(item["start_time"])
        e = parse_time_str(item["end_time"])
        total_meeting_minutes += (e - s)

    finish_time = current_time

    score = {
        "count_met": len(order),
        "total_meeting_minutes": total_meeting_minutes,
        "finish_time": finish_time,
        "total_travel_minutes": total_travel
    }

    return itinerary, score

def better(score_a, score_b):
    # Return True if score_a is better than score_b
    # Criteria:
    # 1) maximize number of people met
    # 2) maximize total meeting minutes
    # 3) minimize finish_time (earlier finish preferred)
    # 4) minimize total travel time
    if score_b is None:
        return True
    if score_a["count_met"] != score_b["count_met"]:
        return score_a["count_met"] > score_b["count_met"]
    if score_a["total_meeting_minutes"] != score_b["total_meeting_minutes"]:
        return score_a["total_meeting_minutes"] > score_b["total_meeting_minutes"]
    if score_a["finish_time"] != score_b["finish_time"]:
        return score_a["finish_time"] < score_b["finish_time"]
    if score_a["total_travel_minutes"] != score_b["total_travel_minutes"]:
        return score_a["total_travel_minutes"] < score_b["total_travel_minutes"]
    return False

# Enumerate schedules over all subsets and permutations to find the best
names = list(people.keys())
best_itinerary = None
best_score = None

for k in range(len(names), 0, -1):
    for subset in combinations(names, k):
        for order in permutations(subset):
            result = compute_schedule_for_order(order)
            if result is None:
                continue
            itinerary, score = result
            if better(score, best_score):
                best_itinerary = itinerary
                best_score = score

# Fallback: if nothing feasible (shouldn't happen here), return empty itinerary
if best_itinerary is None:
    best_itinerary = []

output = {
    "itinerary": best_itinerary
}

print(json.dumps(output, ensure_ascii=False))