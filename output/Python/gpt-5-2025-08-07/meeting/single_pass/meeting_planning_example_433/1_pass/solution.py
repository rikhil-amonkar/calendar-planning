import itertools
import json

# Time helpers
def to_minutes(h, m):
    return h * 60 + m

def m2str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Input data
start_location = "Nob Hill"
start_time = to_minutes(9, 0)

travel = {
    "Nob Hill": {
        "Richmond District": 14,
        "Financial District": 9,
        "North Beach": 8,
        "The Castro": 17,
        "Golden Gate Park": 17
    },
    "Richmond District": {
        "Nob Hill": 17,
        "Financial District": 22,
        "North Beach": 17,
        "The Castro": 16,
        "Golden Gate Park": 9
    },
    "Financial District": {
        "Nob Hill": 8,
        "Richmond District": 21,
        "North Beach": 7,
        "The Castro": 23,
        "Golden Gate Park": 23
    },
    "North Beach": {
        "Nob Hill": 7,
        "Richmond District": 18,
        "Financial District": 8,
        "The Castro": 22,
        "Golden Gate Park": 22
    },
    "The Castro": {
        "Nob Hill": 16,
        "Richmond District": 16,
        "Financial District": 20,
        "North Beach": 20,
        "Golden Gate Park": 11
    },
    "Golden Gate Park": {
        "Nob Hill": 20,
        "Richmond District": 7,
        "Financial District": 26,
        "North Beach": 24,
        "The Castro": 13
    }
}

# People constraints
people = {
    "Emily": {
        "location": "Richmond District",
        "window_start": to_minutes(19, 0),
        "window_end": to_minutes(21, 0),
        "min_duration": 15
    },
    "Margaret": {
        "location": "Financial District",
        "window_start": to_minutes(16, 30),
        "window_end": to_minutes(20, 15),
        "min_duration": 75
    },
    "Ronald": {
        "location": "North Beach",
        "window_start": to_minutes(18, 30),
        "window_end": to_minutes(19, 30),
        "min_duration": 45
    },
    "Deborah": {
        "location": "The Castro",
        "window_start": to_minutes(13, 45),
        "window_end": to_minutes(21, 15),
        "min_duration": 90
    },
    "Jeffrey": {
        "location": "Golden Gate Park",
        "window_start": to_minutes(11, 15),
        "window_end": to_minutes(14, 30),
        "min_duration": 120
    }
}

# Core scheduling function
def schedule_for_order(order):
    cur_loc = start_location
    cur_time = start_time
    itinerary = []
    total_travel = 0

    for person in order:
        info = people[person]
        loc = info["location"]
        wstart = info["window_start"]
        wend = info["window_end"]
        dur = info["min_duration"]

        # Get travel time from current location to person's location
        if cur_loc == loc:
            ttime = 0
        else:
            ttime = travel[cur_loc][loc]
        total_travel += ttime

        # Earliest arrival if we left immediately
        earliest_arrival = cur_time + ttime
        # We can time our departure to arrive right at start if earliest_arrival < wstart
        start_mt = max(earliest_arrival, wstart)
        end_mt = start_mt + dur

        if end_mt > wend:
            return None  # infeasible

        # Record meeting
        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": person,
            "start_time_min": start_mt,
            "end_time_min": end_mt
        })

        # Update current
        cur_loc = loc
        cur_time = end_mt

    return {
        "itinerary": itinerary,
        "total_travel": total_travel,
        "finish_time": cur_time,
        "met_count": len(order)
    }

# Optimize: maximize met_count, then minimize total_travel, then minimize finish_time
names = list(people.keys())
best = None

for k in range(len(names), 0, -1):
    found_any = False
    for perm in itertools.permutations(names, k):
        result = schedule_for_order(perm)
        if result is None:
            continue
        found_any = True
        if best is None:
            best = result
        else:
            if result["met_count"] > best["met_count"]:
                best = result
            elif result["met_count"] == best["met_count"]:
                if result["total_travel"] < best["total_travel"]:
                    best = result
                elif result["total_travel"] == best["total_travel"]:
                    if result["finish_time"] < best["finish_time"]:
                        best = result
    if found_any and best and best["met_count"] == k:
        # cannot do better than meeting k people within this loop; break to keep maximum k
        break

# Convert to requested JSON structure
output = {"itinerary": []}
if best:
    for item in best["itinerary"]:
        output["itinerary"].append({
            "action": "meet",
            "location": item["location"],
            "person": item["person"],
            "start_time": m2str(item["start_time_min"]),
            "end_time": m2str(item["end_time_min"])
        })

print(json.dumps(output))