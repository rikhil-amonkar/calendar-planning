# Solve the SF friend-meeting problem using Z3 by maximizing the number of friends met.
# We check feasibility for subsets and permutations of friends and extract a valid itinerary.

from z3 import Int, Optimize, sat
import itertools
import json

def to_minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h*60 + m

def fmt(mm):
    h = mm // 60
    m = mm % 60
    return f"{h:02d}:{m:02d}"

# Travel times (directed, in minutes)
T = {
    "Presidio": {
        "Marina District": 11, "The Castro": 21, "Fisherman's Wharf": 19, "Bayview": 31,
        "Pacific Heights": 11, "Mission District": 26, "Alamo Square": 19, "Golden Gate Park": 12
    },
    "Marina District": {
        "Presidio": 10, "The Castro": 22, "Fisherman's Wharf": 10, "Bayview": 27,
        "Pacific Heights": 7, "Mission District": 20, "Alamo Square": 15, "Golden Gate Park": 18
    },
    "The Castro": {
        "Presidio": 20, "Marina District": 21, "Fisherman's Wharf": 24, "Bayview": 19,
        "Pacific Heights": 16, "Mission District": 7, "Alamo Square": 8, "Golden Gate Park": 11
    },
    "Fisherman's Wharf": {
        "Presidio": 17, "Marina District": 9, "The Castro": 27, "Bayview": 26,
        "Pacific Heights": 12, "Mission District": 22, "Alamo Square": 21, "Golden Gate Park": 25
    },
    "Bayview": {
        "Presidio": 32, "Marina District": 27, "The Castro": 19, "Fisherman's Wharf": 25,
        "Pacific Heights": 23, "Mission District": 13, "Alamo Square": 16, "Golden Gate Park": 22
    },
    "Pacific Heights": {
        "Presidio": 11, "Marina District": 6, "The Castro": 16, "Fisherman's Wharf": 13,
        "Bayview": 22, "Mission District": 15, "Alamo Square": 10, "Golden Gate Park": 15
    },
    "Mission District": {
        "Presidio": 25, "Marina District": 19, "The Castro": 7, "Fisherman's Wharf": 22,
        "Bayview": 14, "Pacific Heights": 16, "Alamo Square": 11, "Golden Gate Park": 17
    },
    "Alamo Square": {
        "Presidio": 17, "Marina District": 15, "The Castro": 8, "Fisherman's Wharf": 19,
        "Bayview": 16, "Pacific Heights": 10, "Mission District": 10, "Golden Gate Park": 9
    },
    "Golden Gate Park": {
        "Presidio": 11, "Marina District": 16, "The Castro": 13, "Fisherman's Wharf": 24,
        "Bayview": 23, "Pacific Heights": 16, "Mission District": 17, "Alamo Square": 9
    }
}

# People data: location, availability window, min required minutes
people = {
    "Amanda":  {"loc": "Marina District",      "start": to_minutes("14:45"), "end": to_minutes("19:30"), "min": 105},
    "Melissa": {"loc": "The Castro",           "start": to_minutes("09:30"), "end": to_minutes("17:00"), "min": 30},
    "Jeffrey": {"loc": "Fisherman's Wharf",    "start": to_minutes("12:45"), "end": to_minutes("18:45"), "min": 120},
    "Matthew": {"loc": "Bayview",              "start": to_minutes("10:15"), "end": to_minutes("13:15"), "min": 30},
    "Nancy":   {"loc": "Pacific Heights",      "start": to_minutes("17:00"), "end": to_minutes("21:30"), "min": 105},
    "Karen":   {"loc": "Mission District",     "start": to_minutes("17:30"), "end": to_minutes("20:30"), "min": 105},
    "Robert":  {"loc": "Alamo Square",         "start": to_minutes("11:15"), "end": to_minutes("17:30"), "min": 120},
    "Joseph":  {"loc": "Golden Gate Park",     "start": to_minutes("08:30"), "end": to_minutes("21:15"), "min": 105},
}

start_loc = "Presidio"
day_start = to_minutes("09:00")

names = list(people.keys())

def travel(a, b):
    if a == b:
        return 0
    return T[a][b]

def feasible_itinerary(order):
    # Build Z3 Optimize model for a fixed order, enforce sequential travel and time windows
    opt = Optimize()
    n = len(order)
    starts = [Int(f"start_{i}") for i in range(n)]
    ends   = [Int(f"end_{i}")   for i in range(n)]

    for i, name in enumerate(order):
        p = people[name]
        dur = p["min"]
        # time window and duration
        opt.add(starts[i] >= p["start"])
        opt.add(ends[i] == starts[i] + dur)
        opt.add(ends[i] <= p["end"])
        # non-negative times
        opt.add(starts[i] >= 0)
        # travel constraints
        if i == 0:
            opt.add(starts[i] >= day_start + travel(start_loc, p["loc"]))
        else:
            prev = people[order[i-1]]
            opt.add(starts[i] >= ends[i-1] + travel(prev["loc"], p["loc"]))

    # Minimize each start to get the earliest feasible schedule for the chosen order
    for s in starts:
        opt.minimize(s)
    # Also minimize last end as a tie-breaker
    if n > 0:
        opt.minimize(ends[-1])

    if opt.check() != sat:
        return None

    model = opt.model()
    itinerary = []
    for i, name in enumerate(order):
        s = model[starts[i]].as_long()
        e = model[ends[i]].as_long()
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": fmt(s),
            "end_time": fmt(e)
        })
    return itinerary

best_itinerary = None

# Try largest subsets first to maximize the number of friends met
for k in range(len(names), 0, -1):
    found_for_k = False
    # Try all subsets of size k
    for subset in itertools.combinations(names, k):
        # For permutations of the subset, try to find a feasible schedule
        for order in itertools.permutations(subset):
            iti = feasible_itinerary(order)
            if iti is not None:
                best_itinerary = iti
                found_for_k = True
                break
        if found_for_k:
            break
    if found_for_k:
        break

# If nothing found (shouldn't happen), fall back to empty itinerary
if best_itinerary is None:
    best_itinerary = []

# Print the JSON dictionary as required
print(json.dumps({"itinerary": best_itinerary}, ensure_ascii=False))