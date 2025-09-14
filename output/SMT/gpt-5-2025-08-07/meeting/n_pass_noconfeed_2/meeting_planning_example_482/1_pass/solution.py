# SOLUTION:
import json
from z3 import *

def minutes(h, m):
    return h * 60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Locations
locations = [
    "Haight-Ashbury",
    "Mission District",
    "Bayview",
    "Pacific Heights",
    "Russian Hill",
    "Fisherman's Wharf",
]

# Travel times (in minutes)
travel = {
    "Haight-Ashbury": {
        "Mission District": 11,
        "Bayview": 18,
        "Pacific Heights": 12,
        "Russian Hill": 17,
        "Fisherman's Wharf": 23,
    },
    "Mission District": {
        "Haight-Ashbury": 12,
        "Bayview": 15,
        "Pacific Heights": 16,
        "Russian Hill": 15,
        "Fisherman's Wharf": 22,
    },
    "Bayview": {
        "Haight-Ashbury": 19,
        "Mission District": 13,
        "Pacific Heights": 23,
        "Russian Hill": 23,
        "Fisherman's Wharf": 25,
    },
    "Pacific Heights": {
        "Haight-Ashbury": 11,
        "Mission District": 15,
        "Bayview": 22,
        "Russian Hill": 7,
        "Fisherman's Wharf": 13,
    },
    "Russian Hill": {
        "Haight-Ashbury": 17,
        "Mission District": 16,
        "Bayview": 23,
        "Pacific Heights": 7,
        "Fisherman's Wharf": 7,
    },
    "Fisherman's Wharf": {
        "Haight-Ashbury": 22,
        "Mission District": 22,
        "Bayview": 26,
        "Pacific Heights": 12,
        "Russian Hill": 7,
    },
}

# Zero travel for same-location moves
for a in locations:
    travel[a][a] = 0

# Start info
start_location = "Haight-Ashbury"
start_time = minutes(9, 0)

# People constraints
people = [
    {
        "name": "Stephanie",
        "location": "Mission District",
        "avail_start": minutes(8, 15),
        "avail_end": minutes(13, 45),
        "min_duration": 90,
    },
    {
        "name": "Sandra",
        "location": "Bayview",
        "avail_start": minutes(13, 0),
        "avail_end": minutes(19, 30),
        "min_duration": 15,
    },
    {
        "name": "Richard",
        "location": "Pacific Heights",
        "avail_start": minutes(7, 15),
        "avail_end": minutes(10, 15),
        "min_duration": 75,
    },
    {
        "name": "Brian",
        "location": "Russian Hill",
        "avail_start": minutes(12, 15),
        "avail_end": minutes(16, 0),
        "min_duration": 120,
    },
    {
        "name": "Jason",
        "location": "Fisherman's Wharf",
        "avail_start": minutes(8, 30),
        "avail_end": minutes(17, 45),
        "min_duration": 60,
    },
]

n = len(people)

# Z3 variables
opt = Optimize()

starts = [Int(f"start_{i}") for i in range(n)]
ends = [Int(f"end_{i}") for i in range(n)]
meets = [Bool(f"meet_{i}") for i in range(n)]

# Domain constraints
for i in range(n):
    opt.add(starts[i] >= 0, ends[i] >= 0, starts[i] <= 24*60, ends[i] <= 24*60, ends[i] >= starts[i])

# Meeting constraints
for i, p in enumerate(people):
    s, e, m = starts[i], ends[i], meets[i]
    opt.add(Implies(m, s >= p["avail_start"]))
    opt.add(Implies(m, e <= p["avail_end"]))
    opt.add(Implies(m, e - s >= p["min_duration"]))

# Pairwise non-overlap with travel time (if both meetings are chosen)
def ttime(loc_a, loc_b):
    return travel[loc_a][loc_b]

for i in range(n):
    for j in range(i + 1, n):
        li = people[i]["location"]
        lj = people[j]["location"]
        opt.add(Implies(And(meets[i], meets[j]),
                        Or(ends[i] + ttime(li, lj) <= starts[j],
                           ends[j] + ttime(lj, li) <= starts[i])))

# Reachability from start (every met meeting must be reachable either from start or from a previous meeting)
for i in range(n):
    li = people[i]["location"]
    preds = [starts[i] >= start_time + ttime(start_location, li)]
    for j in range(n):
        if j == i:
            continue
        lj = people[j]["location"]
        preds.append(And(meets[j], ends[j] + ttime(lj, li) <= starts[i]))
    opt.add(Implies(meets[i], Or(preds)))

# Objective: maximize number of people met, then maximize total meeting time
sum_met = Sum([If(meets[i], 1, 0) for i in range(n)])
sum_minutes = Sum([If(meets[i], ends[i] - starts[i], 0) for i in range(n)])

opt.maximize(sum_met)
opt.maximize(sum_minutes)

result = {"itinerary": []}

if opt.check() == sat:
    model = opt.model()
    chosen = []
    for i, p in enumerate(people):
        if is_true(model.eval(meets[i])):
            s_val = model.eval(starts[i]).as_long()
            e_val = model.eval(ends[i]).as_long()
            chosen.append((s_val, e_val, p["location"], p["name"]))
    # Sort by start time
    chosen.sort(key=lambda x: x[0])
    for s_val, e_val, loc, person in chosen:
        result["itinerary"].append({
            "action": "meet",
            "location": loc,
            "person": person,
            "start_time": fmt_time(s_val),
            "end_time": fmt_time(e_val),
        })

print(json.dumps(result, ensure_ascii=False))