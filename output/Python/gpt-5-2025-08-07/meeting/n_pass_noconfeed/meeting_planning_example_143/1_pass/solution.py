"SOLUTION:"

import json
import itertools

# Helper functions
def parse_time(t):
    # Expects format H:MM or HH:MM in 24-hour clock
    h, m = t.split(":")
    return int(h) * 60 + int(m)

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input variables
start_location = "North Beach"
start_time_str = "9:00"

# Travel times in minutes (directed)
travel_minutes = {
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Embarcadero"): 6,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Embarcadero"): 10,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Pacific Heights"): 11,
}

friends = [
    {
        "name": "Karen",
        "location": "Pacific Heights",
        "start": "18:45",
        "end": "20:15",
        "min_minutes": 90,
    },
    {
        "name": "Mark",
        "location": "Embarcadero",
        "start": "13:00",
        "end": "17:45",
        "min_minutes": 120,
    },
]

# Preprocess times
start_time = parse_time(start_time_str)
for f in friends:
    f["start_min"] = parse_time(f["start"])
    f["end_min"] = parse_time(f["end"])

# Utility: travel time lookup
def travel_time(frm, to):
    return travel_minutes[(frm, to)]

# Plan a given ordered sequence of friends
def plan_sequence(order):
    time = start_time
    loc = start_location
    itinerary = []
    waiting_total = 0

    for i, f in enumerate(order):
        # Travel to friend
        T = travel_time(loc, f["location"])
        earliest_arrival = time + T

        # We can delay departure to align with window start to minimize idle/early arrival
        start_i = max(earliest_arrival, f["start_min"])
        # Waiting before departure from current location (idle time)
        dep_time = start_i - T
        if dep_time > time:
            waiting_total += dep_time - time

        # Feasibility check for meeting duration and future constraints
        if i < len(order) - 1:
            nxt = order[i + 1]
            T_next = travel_time(f["location"], nxt["location"])

            # If we can end by f["end_min"] and arrive before nxt window opens (so we can wait),
            # then the max end is simply f["end_min"]
            if f["end_min"] <= nxt["start_min"] - T_next:
                end_i_max = f["end_min"]
            else:
                # Otherwise we must finish early enough to still fit next min meeting
                end_i_max = min(f["end_min"], nxt["end_min"] - nxt["min_minutes"] - T_next)

            end_i_min = start_i + f["min_minutes"]
            if end_i_max < end_i_min:
                return None  # infeasible
            end_i = end_i_max  # choose maximum allowed to maximize total meeting time
        else:
            # Last friend: maximize meeting time within their window
            if start_i + f["min_minutes"] > f["end_min"]:
                return None
            end_i = f["end_min"]

        itinerary.append({
            "action": "meet",
            "location": f["location"],
            "person": f["name"],
            "start_time": fmt_time(start_i),
            "end_time": fmt_time(end_i),
            "_start_min": start_i,
            "_end_min": end_i
        })

        # Update current state
        time = end_i
        loc = f["location"]

    # Compute total meeting minutes
    total_meeting = sum(item["_end_min"] - item["_start_min"] for item in itinerary)

    # Clean internal fields
    for item in itinerary:
        item.pop("_start_min", None)
        item.pop("_end_min", None)

    return {
        "itinerary": itinerary,
        "num_met": len(itinerary),
        "total_meeting": total_meeting,
        "waiting": waiting_total
    }

# Generate and evaluate plans for all non-empty subsets and their orders
best_plan = None
for r in range(1, len(friends) + 1):
    for subset in itertools.permutations(friends, r):
        plan = plan_sequence(list(subset))
        if plan is None:
            continue
        if best_plan is None:
            best_plan = plan
        else:
            # Optimize: max friends met, then max total meeting, then min waiting
            key_best = (best_plan["num_met"], best_plan["total_meeting"], -best_plan["waiting"])
            key_curr = (plan["num_met"], plan["total_meeting"], -plan["waiting"])
            if key_curr > key_best:
                best_plan = plan

# Fallback to empty itinerary if nothing feasible (shouldn't happen with given data)
output = {"itinerary": best_plan["itinerary"] if best_plan else []}

print(json.dumps(output, ensure_ascii=False))