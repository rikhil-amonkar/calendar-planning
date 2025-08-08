import itertools
import json

# Time helpers
def to_minutes(h, m):
    return h * 60 + m

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input variables (constraints)
start_location = "Bayview"
start_time = to_minutes(9, 0)

people = {
    "Joseph": {
        "location": "Russian Hill",
        "window_start": to_minutes(8, 30),
        "window_end": to_minutes(19, 15),
        "min_duration": 60
    },
    "Nancy": {
        "location": "Alamo Square",
        "window_start": to_minutes(11, 0),
        "window_end": to_minutes(16, 0),
        "min_duration": 90
    },
    "Jason": {
        "location": "North Beach",
        "window_start": to_minutes(16, 45),
        "window_end": to_minutes(21, 45),
        "min_duration": 15
    },
    "Jeffrey": {
        "location": "Financial District",
        "window_start": to_minutes(10, 30),
        "window_end": to_minutes(15, 45),
        "min_duration": 45
    }
}

# Travel times (in minutes)
travel = {
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "North Beach"): 21,
    ("Bayview", "Financial District"): 19,

    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Financial District"): 11,

    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Financial District"): 17,

    ("North Beach", "Bayview"): 22,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Financial District"): 8,

    ("Financial District", "Bayview"): 19,
    ("Financial District", "Russian Hill"): 10,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "North Beach"): 7,
}

def get_travel_time(a, b):
    if (a, b) in travel:
        return travel[(a, b)]
    else:
        # In case of missing pair (should not happen given inputs), assume symmetric or raise error
        if (b, a) in travel:
            return travel[(b, a)]
        raise ValueError(f"No travel time between {a} and {b}")

def schedule_for_order(order):
    current_loc = start_location
    current_time = start_time
    itinerary = []
    total_wait = 0
    total_travel = 0

    for person in order:
        info = people[person]
        loc = info["location"]
        t_travel = get_travel_time(current_loc, loc)
        arrival = current_time + t_travel
        total_travel += t_travel

        start_meet = max(arrival, info["window_start"])
        wait_here = max(0, start_meet - arrival)
        total_wait += wait_here

        end_meet = start_meet + info["min_duration"]
        if end_meet > info["window_end"]:
            return None  # infeasible

        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": person,
            "start_time": fmt_time(start_meet),
            "end_time": fmt_time(end_meet)
        })

        current_loc = loc
        current_time = end_meet

    finish_time = current_time
    return {
        "itinerary": itinerary,
        "finish_time": finish_time,
        "total_wait": total_wait,
        "total_travel": total_travel,
        "count": len(order)
    }

# Search all subsets and permutations to maximize number of friends met.
names = list(people.keys())
best = None

for r in range(len(names), 0, -1):
    found_any = False
    for subset in itertools.combinations(names, r):
        for perm in itertools.permutations(subset):
            result = schedule_for_order(perm)
            if result is None:
                continue
            found_any = True
            if best is None:
                best = result
            else:
                # Objective: maximize count, then minimize finish_time, then minimize total_wait, then minimize total_travel, then lexicographic itinerary as final tie-breaker
                a = best
                b = result
                key_a = (-a["count"], a["finish_time"], a["total_wait"], a["total_travel"], [i["person"] for i in a["itinerary"]])
                key_b = (-b["count"], b["finish_time"], b["total_wait"], b["total_travel"], [i["person"] for i in b["itinerary"]])
                if key_b < key_a:
                    best = result
    if found_any:
        break  # we found at least one feasible schedule with r persons, no need to consider smaller subsets

# Output
output = {"itinerary": best["itinerary"] if best else []}
print(json.dumps(output))