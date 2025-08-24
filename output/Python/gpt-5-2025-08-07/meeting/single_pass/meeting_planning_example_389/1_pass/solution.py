# SOLUTION:
import json
import itertools

def time_to_str(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Input parameters
start_location = "Haight-Ashbury"
start_time = 9 * 60  # 9:00 in minutes

# Travel times (directed, minutes)
travel = {
    "Haight-Ashbury": {
        "Fisherman's Wharf": 23,
        "Richmond District": 10,
        "Mission District": 11,
        "Bayview": 18,
    },
    "Fisherman's Wharf": {
        "Haight-Ashbury": 22,
        "Richmond District": 18,
        "Mission District": 22,
        "Bayview": 26,
    },
    "Richmond District": {
        "Haight-Ashbury": 10,
        "Fisherman's Wharf": 18,
        "Mission District": 20,
        "Bayview": 26,
    },
    "Mission District": {
        "Haight-Ashbury": 12,
        "Fisherman's Wharf": 22,
        "Richmond District": 20,
        "Bayview": 15,
    },
    "Bayview": {
        "Haight-Ashbury": 19,
        "Fisherman's Wharf": 25,
        "Richmond District": 25,
        "Mission District": 13,
    },
}

# Friends constraints
friends = {
    "Sarah": {
        "location": "Fisherman's Wharf",
        "window_start": 14 * 60 + 45,  # 14:45
        "window_end": 17 * 60 + 30,    # 17:30
        "min_duration": 105,
    },
    "Mary": {
        "location": "Richmond District",
        "window_start": 13 * 60,       # 13:00
        "window_end": 19 * 60 + 15,    # 19:15
        "min_duration": 75,
    },
    "Helen": {
        "location": "Mission District",
        "window_start": 21 * 60 + 45,  # 21:45
        "window_end": 22 * 60 + 30,    # 22:30
        "min_duration": 30,
    },
    "Thomas": {
        "location": "Bayview",
        "window_start": 15 * 60 + 15,  # 15:15
        "window_end": 18 * 60 + 45,    # 18:45
        "min_duration": 120,
    },
}

def evaluate_order(order):
    current_loc = start_location
    current_time = start_time
    itinerary = []
    total_travel = 0
    total_wait = 0
    total_meet = 0

    for name in order:
        info = friends[name]
        loc = info["location"]
        w_start = info["window_start"]
        w_end = info["window_end"]
        dur = info["min_duration"]

        # Get travel time; if missing, infeasible
        if current_loc not in travel or loc not in travel[current_loc]:
            return None

        t_travel = travel[current_loc][loc]
        arrive_time = current_time + t_travel

        # We can always choose to depart later to reduce idle time; the earliest feasible meeting start is:
        meet_start = max(arrive_time, w_start)
        meet_end = meet_start + dur

        if meet_end > w_end:
            return None  # infeasible

        # Idle time before meeting (not traveling)
        idle = max(0, meet_start - arrive_time)
        total_wait += idle
        total_travel += t_travel
        total_meet += dur

        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": name,
            "start_time": time_to_str(meet_start),
            "end_time": time_to_str(meet_end),
        })

        # Advance
        current_time = meet_end
        current_loc = loc

    finish_time = current_time
    return {
        "itinerary": itinerary,
        "metrics": {
            "count": len(itinerary),
            "total_wait": total_wait,
            "total_travel": total_travel,
            "total_meet": total_meet,
            "finish_time": finish_time,
            "order": order,
        }
    }

# Search across all subsets and permutations to maximize number of friends met
names = list(friends.keys())
best = None

# Iterate over subset sizes from largest to smallest
for r in range(len(names), 0, -1):
    any_feasible_at_r = False
    for subset in itertools.combinations(names, r):
        for perm in itertools.permutations(subset):
            result = evaluate_order(perm)
            if result is None:
                continue
            any_feasible_at_r = True
            metrics = result["metrics"]

            if best is None:
                best = result
            else:
                b = best["metrics"]
                # Objective: maximize count, then minimize total_wait, then minimize total_travel,
                # then earliest finish_time, then maximize total_meet, then lexicographically smallest order
                key_new = (-metrics["count"], metrics["total_wait"], metrics["total_travel"], metrics["finish_time"], -metrics["total_meet"], metrics["order"])
                key_old = (-b["count"], b["total_wait"], b["total_travel"], b["finish_time"], -b["total_meet"], b["order"])
                if key_new < key_old:
                    best = result
    if any_feasible_at_r:
        break  # No need to check smaller subsets once we found feasible at this size

# Build final JSON output
output = {"itinerary": []}
if best is not None:
    output["itinerary"] = best["itinerary"]

print(json.dumps(output, ensure_ascii=False))