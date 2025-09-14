import json
from z3 import Optimize, Int, Bool, And, Or, If, Not, Implies, Sum, sat

# Helper to convert "H:MM" to minutes since midnight
def to_minutes(t):
    h, m = t.split(":")
    return int(h) * 60 + int(m)

def from_minutes(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

# Travel times (minutes) between neighborhoods (directed)
travel = {
    "Presidio": {
        "Marina District": 11,
        "The Castro": 21,
        "Fisherman's Wharf": 19,
        "Bayview": 31,
        "Pacific Heights": 11,
        "Mission District": 26,
        "Alamo Square": 19,
        "Golden Gate Park": 12,
    },
    "Marina District": {
        "Presidio": 10,
        "The Castro": 22,
        "Fisherman's Wharf": 10,
        "Bayview": 27,
        "Pacific Heights": 7,
        "Mission District": 20,
        "Alamo Square": 15,
        "Golden Gate Park": 18,
    },
    "The Castro": {
        "Presidio": 20,
        "Marina District": 21,
        "Fisherman's Wharf": 24,
        "Bayview": 19,
        "Pacific Heights": 16,
        "Mission District": 7,
        "Alamo Square": 8,
        "Golden Gate Park": 11,
    },
    "Fisherman's Wharf": {
        "Presidio": 17,
        "Marina District": 9,
        "The Castro": 27,
        "Bayview": 26,
        "Pacific Heights": 12,
        "Mission District": 22,
        "Alamo Square": 21,
        "Golden Gate Park": 25,
    },
    "Bayview": {
        "Presidio": 32,
        "Marina District": 27,
        "The Castro": 19,
        "Fisherman's Wharf": 25,
        "Pacific Heights": 23,
        "Mission District": 13,
        "Alamo Square": 16,
        "Golden Gate Park": 22,
    },
    "Pacific Heights": {
        "Presidio": 11,
        "Marina District": 6,
        "The Castro": 16,
        "Fisherman's Wharf": 13,
        "Bayview": 22,
        "Mission District": 15,
        "Alamo Square": 10,
        "Golden Gate Park": 15,
    },
    "Mission District": {
        "Presidio": 25,
        "Marina District": 19,
        "The Castro": 7,
        "Fisherman's Wharf": 22,
        "Bayview": 14,
        "Pacific Heights": 16,
        "Alamo Square": 11,
        "Golden Gate Park": 17,
    },
    "Alamo Square": {
        "Presidio": 17,
        "Marina District": 15,
        "The Castro": 8,
        "Fisherman's Wharf": 19,
        "Bayview": 16,
        "Pacific Heights": 10,
        "Mission District": 10,
        "Golden Gate Park": 9,
    },
    "Golden Gate Park": {
        "Presidio": 11,
        "Marina District": 16,
        "The Castro": 13,
        "Fisherman's Wharf": 24,
        "Bayview": 23,
        "Pacific Heights": 16,
        "Mission District": 17,
        "Alamo Square": 9,
    },
}

# Ensure self-travel is zero and all keys exist
locations = list(travel.keys())
for a in locations:
    if a not in travel:
        travel[a] = {}
    for b in locations:
        if a == b:
            travel[a][b] = 0
        else:
            # Some dicts might be missing reverse entries; we keep as provided (directed)
            if b not in travel[a]:
                # If a missing directed edge exists, conservatively set a large travel to discourage/forbid its use
                travel[a][b] = 10**6

# People constraints
people = [
    {"name": "Amanda",  "location": "Marina District",      "start": "14:45", "end": "19:30", "min_minutes": 105},
    {"name": "Melissa", "location": "The Castro",           "start": "9:30",  "end": "17:00", "min_minutes": 30},
    {"name": "Jeffrey", "location": "Fisherman's Wharf",    "start": "12:45", "end": "18:45", "min_minutes": 120},
    {"name": "Matthew", "location": "Bayview",              "start": "10:15", "end": "13:15", "min_minutes": 30},
    {"name": "Nancy",   "location": "Pacific Heights",      "start": "17:00", "end": "21:30", "min_minutes": 105},
    {"name": "Karen",   "location": "Mission District",     "start": "17:30", "end": "20:30", "min_minutes": 105},
    {"name": "Robert",  "location": "Alamo Square",         "start": "11:15", "end": "17:30", "min_minutes": 120},
    {"name": "Joseph",  "location": "Golden Gate Park",     "start": "8:30",  "end": "21:15", "min_minutes": 105},
]

# Convert time strings to minutes
for p in people:
    p["start_min"] = to_minutes(p["start"])
    p["end_min"] = to_minutes(p["end"])

# Arrival info
origin_location = "Presidio"
arrival_time_min = to_minutes("9:00")

opt = Optimize()
opt.set(priority='lex')

# Z3 variables
start_vars = {}
end_vars = {}
meet_bools = {}

for p in people:
    key = p["name"].replace(" ", "_")
    start_vars[key] = Int(f"start_{key}")
    end_vars[key] = Int(f"end_{key}")
    meet_bools[key] = Bool(f"meet_{key}")

# Constraints per person
for p in people:
    key = p["name"].replace(" ", "_")
    s = start_vars[key]
    e = end_vars[key]
    m = meet_bools[key]
    loc = p["location"]
    avail_s = p["start_min"]
    avail_e = p["end_min"]
    min_dur = p["min_minutes"]
    origin_reach = arrival_time_min + travel[origin_location][loc]

    # If meeting, times within availability and meet minimum duration and reachable from origin
    opt.add(Implies(m, And(
        s >= avail_s,
        e <= avail_e,
        e - s >= min_dur,
        s >= origin_reach
    )))
    # If not meeting, zero times
    opt.add(Implies(Not(m), And(s == 0, e == 0)))

# Pairwise non-overlap and travel-time sequencing
n = len(people)
order_bools = {}
for i in range(n):
    for j in range(i + 1, n):
        pi = people[i]
        pj = people[j]
        ki = pi["name"].replace(" ", "_")
        kj = pj["name"].replace(" ", "_")
        bi = meet_bools[ki]
        bj = meet_bools[kj]
        si = start_vars[ki]
        ei = end_vars[ki]
        sj = start_vars[kj]
        ej = end_vars[kj]
        order_ij = Bool(f"order_{ki}_before_{kj}")
        order_bools[(ki, kj)] = order_ij

        ti_to_j = travel[pi["location"]][pj["location"]]
        tj_to_i = travel[pj["location"]][pi["location"]]

        # If both meetings happen, enforce one ordering with travel time
        opt.add(Implies(And(bi, bj, order_ij), sj >= ei + ti_to_j))
        opt.add(Implies(And(bi, bj, Not(order_ij)), si >= ej + tj_to_i))

# Objectives: maximize number of friends met, then maximize total meeting time
met_count = Sum([If(meet_bools[p["name"].replace(" ", "_")], 1, 0) for p in people])
total_meet_time = Sum([end_vars[p["name"].replace(" ", "_")] - start_vars[p["name"].replace(" ", "_")] for p in people])

opt.maximize(met_count)
opt.maximize(total_meet_time)

if opt.check() != sat:
    # If unsat, output empty itinerary
    print(json.dumps({"itinerary": []}))
else:
    model = opt.model()
    itinerary = []
    # Collect meetings
    for p in people:
        key = p["name"].replace(" ", "_")
        if model.evaluate(meet_bools[key], model_completion=True):
            s = model.evaluate(start_vars[key]).as_long()
            e = model.evaluate(end_vars[key]).as_long()
            itinerary.append({
                "action": "meet",
                "location": p["location"],
                "person": p["name"],
                "start_time": from_minutes(s),
                "end_time": from_minutes(e),
            })
    # Sort by start time
    itinerary.sort(key=lambda x: to_minutes(x["start_time"]))
    print(json.dumps({"itinerary": itinerary}))