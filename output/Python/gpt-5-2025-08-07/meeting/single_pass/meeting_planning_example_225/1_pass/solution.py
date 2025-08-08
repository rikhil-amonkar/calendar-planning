import itertools
import json

# Time helpers
def htom(t):
    # Convert H:MM string to minutes since midnight
    h, m = t.split(":")
    return int(h) * 60 + int(m)

def mtoh(m):
    # Convert minutes since midnight to H:MM (24-hour, no leading zero on hour)
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Input variables: locations and travel times (in minutes)
locations = ["Sunset District", "North Beach", "Union Square", "Alamo Square"]

travel = {
    ("Sunset District", "North Beach"): 29,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Alamo Square"): 17,

    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Alamo Square"): 16,

    ("Union Square", "Sunset District"): 26,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Alamo Square"): 15,

    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Union Square"): 14,
}

# Constraints: availability windows and minimum meeting durations
friends = {
    "Sarah":   {"location": "North Beach",   "start": htom("16:00"), "end": htom("18:15"), "min_dur": 60},
    "Jeffrey": {"location": "Union Square",  "start": htom("15:00"), "end": htom("22:00"), "min_dur": 75},
    "Brian":   {"location": "Alamo Square",  "start": htom("16:00"), "end": htom("17:30"), "min_dur": 75},
}

start_location = "Sunset District"
start_time = htom("9:00")

def travel_time(a, b):
    if a == b:
        return 0
    return travel[(a, b)]

def try_schedule(order):
    time = start_time
    loc = start_location
    itinerary = []
    total_travel = 0
    total_wait = 0

    for person in order:
        info = friends[person]
        to_loc = info["location"]
        t_travel = travel_time(loc, to_loc)
        arrival = time + t_travel
        total_travel += t_travel

        start_meet = max(arrival, info["start"])
        wait = max(0, start_meet - arrival)
        total_wait += wait

        end_meet = start_meet + info["min_dur"]
        if end_meet > info["end"]:
            return None  # infeasible for this order

        itinerary.append({
            "action": "meet",
            "location": to_loc,
            "person": person,
            "start_time": mtoh(start_meet),
            "end_time": mtoh(end_meet),
        })

        time = end_meet
        loc = to_loc

    return {
        "itinerary": itinerary,
        "total_travel": total_travel,
        "total_wait": total_wait,
        "end_time": time,
        "met_count": len(order),
        "order": order,
    }

def select_best(candidates):
    # Optimize:
    # 1) maximize number met (handled by considering fixed met_count sets)
    # 2) minimize total travel time
    # 3) minimize end time
    # 4) minimize total waiting time
    best = None
    best_key = None
    for c in candidates:
        key = (c["total_travel"], c["end_time"], c["total_wait"])
        if best is None or key < best_key:
            best = c
            best_key = key
    return best

def compute_best_schedule():
    names = list(friends.keys())
    n = len(names)
    # Try from maximum number of meetings down to 1
    for k in range(n, 0, -1):
        feasible = []
        for subset in itertools.combinations(names, k):
            for order in itertools.permutations(subset):
                res = try_schedule(order)
                if res is not None:
                    feasible.append(res)
        if feasible:
            return select_best(feasible)
    return {"itinerary": []}

best = compute_best_schedule()
output = {"itinerary": best["itinerary"] if "itinerary" in best else []}
print(json.dumps(output, ensure_ascii=False))