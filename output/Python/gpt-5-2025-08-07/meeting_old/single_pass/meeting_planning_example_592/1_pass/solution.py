import json
from itertools import permutations, combinations

def hm(h, m):
    return h * 60 + m

def fmt(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times in minutes (directed)
TT = {
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Nob Hill"): 7,

    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Nob Hill"): 8,

    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Mission District"): 18,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Nob Hill"): 8,

    ("Union Square", "North Beach"): 10,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Nob Hill"): 9,

    ("Mission District", "North Beach"): 17,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Nob Hill"): 12,

    ("Golden Gate Park", "North Beach"): 24,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Nob Hill"): 20,

    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Golden Gate Park"): 17,
}

# Friends constraints
friends = [
    {"name": "James", "location": "Pacific Heights", "start": hm(20, 0), "end": hm(22, 0), "min": 120},
    {"name": "Robert", "location": "Chinatown", "start": hm(12, 15), "end": hm(16, 45), "min": 90},
    {"name": "Jeffrey", "location": "Union Square", "start": hm(9, 30), "end": hm(15, 30), "min": 120},
    {"name": "Carol", "location": "Mission District", "start": hm(18, 15), "end": hm(21, 15), "min": 15},
    {"name": "Mark", "location": "Golden Gate Park", "start": hm(11, 30), "end": hm(17, 45), "min": 15},
    {"name": "Sandra", "location": "Nob Hill", "start": hm(8, 0), "end": hm(15, 30), "min": 15},
]

start_location = "North Beach"
start_time = hm(9, 0)

def simulate(order):
    t = start_time
    loc = start_location
    itinerary = []
    total_wait = 0
    total_meet = 0

    for f in order:
        key = (loc, f["location"])
        if key not in TT:
            return None  # No travel time info; infeasible path
        travel = TT[key]
        arrive = t + travel
        start_meet = max(arrive, f["start"])
        if start_meet + f["min"] > f["end"]:
            return None  # Cannot satisfy minimum within window
        if arrive < f["start"]:
            total_wait += f["start"] - arrive
        end_meet = start_meet + f["min"]
        total_meet += f["min"]
        itinerary.append({
            "action": "meet",
            "location": f["location"],
            "person": f["name"],
            "start_time": fmt(start_meet),
            "end_time": fmt(end_meet),
        })
        t = end_meet
        loc = f["location"]

    return {
        "itinerary": itinerary,
        "end_time": t,
        "total_wait": total_wait,
        "total_meet": total_meet,
        "count": len(order),
    }

def find_best_schedule():
    n = len(friends)
    best = None

    # Try to meet as many as possible: check subsets from size n down to 1
    for k in range(n, 0, -1):
        found_any = False
        # For size n, there's only one subset: all friends
        for subset in combinations(friends, k):
            # Explore all orders
            for order in permutations(subset):
                res = simulate(order)
                if res is None:
                    continue
                found_any = True
                if best is None:
                    best = res
                else:
                    # Primary: maximize number of friends
                    if res["count"] > best["count"]:
                        best = res
                    elif res["count"] == best["count"]:
                        # Secondary: minimize total waiting time
                        if res["total_wait"] < best["total_wait"]:
                            best = res
                        elif res["total_wait"] == best["total_wait"]:
                            # Tertiary: earliest finish time
                            if res["end_time"] < best["end_time"]:
                                best = res
        if found_any:
            break
    return best

best_schedule = find_best_schedule()
output = {"itinerary": best_schedule["itinerary"] if best_schedule else []}
print(json.dumps(output))