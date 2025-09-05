import json
from z3 import *

def minutes(h, m):
    return h * 60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Travel times (minutes) between locations
times = {
    "Mission District": {
        "Alamo Square": 11,
        "Presidio": 25,
        "Russian Hill": 15,
        "North Beach": 17,
        "Golden Gate Park": 17,
        "Richmond District": 20,
        "Embarcadero": 19,
        "Financial District": 15,
        "Marina District": 19,
    },
    "Alamo Square": {
        "Mission District": 10,
        "Presidio": 17,
        "Russian Hill": 13,
        "North Beach": 15,
        "Golden Gate Park": 9,
        "Richmond District": 11,
        "Embarcadero": 16,
        "Financial District": 17,
        "Marina District": 15,
    },
    "Presidio": {
        "Mission District": 26,
        "Alamo Square": 19,
        "Russian Hill": 14,
        "North Beach": 18,
        "Golden Gate Park": 12,
        "Richmond District": 7,
        "Embarcadero": 20,
        "Financial District": 23,
        "Marina District": 11,
    },
    "Russian Hill": {
        "Mission District": 16,
        "Alamo Square": 15,
        "Presidio": 14,
        "North Beach": 5,
        "Golden Gate Park": 21,
        "Richmond District": 14,
        "Embarcadero": 8,
        "Financial District": 11,
        "Marina District": 7,
    },
    "North Beach": {
        "Mission District": 18,
        "Alamo Square": 16,
        "Presidio": 17,
        "Russian Hill": 4,
        "Golden Gate Park": 22,
        "Richmond District": 18,
        "Embarcadero": 6,
        "Financial District": 8,
        "Marina District": 9,
    },
    "Golden Gate Park": {
        "Mission District": 17,
        "Alamo Square": 9,
        "Presidio": 11,
        "Russian Hill": 19,
        "North Beach": 23,
        "Richmond District": 7,
        "Embarcadero": 25,
        "Financial District": 26,
        "Marina District": 16,
    },
    "Richmond District": {
        "Mission District": 20,
        "Alamo Square": 13,
        "Presidio": 7,
        "Russian Hill": 13,
        "North Beach": 17,
        "Golden Gate Park": 9,
        "Embarcadero": 19,
        "Financial District": 22,
        "Marina District": 9,
    },
    "Embarcadero": {
        "Mission District": 20,
        "Alamo Square": 19,
        "Presidio": 20,
        "Russian Hill": 8,
        "North Beach": 5,
        "Golden Gate Park": 25,
        "Richmond District": 21,
        "Financial District": 5,
        "Marina District": 12,
    },
    "Financial District": {
        "Mission District": 17,
        "Alamo Square": 17,
        "Presidio": 22,
        "Russian Hill": 11,
        "North Beach": 7,
        "Golden Gate Park": 23,
        "Richmond District": 21,
        "Embarcadero": 4,
        "Marina District": 15,
    },
    "Marina District": {
        "Mission District": 20,
        "Alamo Square": 15,
        "Presidio": 10,
        "Russian Hill": 8,
        "North Beach": 11,
        "Golden Gate Park": 18,
        "Richmond District": 11,
        "Embarcadero": 14,
        "Financial District": 17,
    },
}

# Add zero travel times for same-location moves
for a in times.keys():
    times[a][a] = 0

def travel(a, b):
    return times[a][b]

origin = "Mission District"
arrival_time = minutes(9, 0)

# People constraints
people = [
    {"name": "Laura", "location": "Alamo Square",      "avail_start": minutes(14, 30), "avail_end": minutes(16, 15), "min_dur": 75},
    {"name": "Brian", "location": "Presidio",          "avail_start": minutes(10, 15), "avail_end": minutes(17, 0),  "min_dur": 30},
    {"name": "Karen", "location": "Russian Hill",      "avail_start": minutes(18, 0),  "avail_end": minutes(20, 15), "min_dur": 90},
    {"name": "Stephanie", "location": "North Beach",   "avail_start": minutes(10, 15), "avail_end": minutes(16, 0),  "min_dur": 75},
    {"name": "Helen", "location": "Golden Gate Park",  "avail_start": minutes(11, 30), "avail_end": minutes(21, 45), "min_dur": 120},
    {"name": "Sandra", "location": "Richmond District","avail_start": minutes(8, 0),   "avail_end": minutes(15, 15), "min_dur": 30},
    {"name": "Mary", "location": "Embarcadero",        "avail_start": minutes(16, 45), "avail_end": minutes(18, 45), "min_dur": 120},
    {"name": "Deborah", "location": "Financial District","avail_start": minutes(19, 0),"avail_end": minutes(20, 45), "min_dur": 105},
    {"name": "Elizabeth", "location": "Marina District","avail_start": minutes(8, 30), "avail_end": minutes(13, 15), "min_dur": 105},
]

n = len(people)

# Z3 variables
meet = []
start = []
end = []

opt = Optimize()

for i, p in enumerate(people):
    meet_i = Bool(f"meet_{i}")
    start_i = Int(f"start_{i}")
    end_i = Int(f"end_{i}")
    meet.append(meet_i)
    start.append(start_i)
    end.append(end_i)

    # Bounds on times
    opt.add(start_i >= 0, start_i <= 24*60)
    opt.add(end_i >= 0, end_i <= 24*60)

    # Meeting constraints: within availability, exact minimum duration (for determinism), and reachable from origin
    opt.add(Implies(meet_i, And(
        start_i >= p["avail_start"],
        end_i <= p["avail_end"],
        end_i - start_i == p["min_dur"],
        start_i >= arrival_time + travel(origin, p["location"])
    )))
    # If not meeting, collapse interval
    opt.add(Implies(Not(meet_i), end_i == start_i))

# Non-overlap with travel time between any two meetings
for i in range(n):
    for j in range(i+1, n):
        li = people[i]["location"]
        lj = people[j]["location"]
        tij = travel(li, lj)
        tji = travel(lj, li)
        opt.add(Implies(And(meet[i], meet[j]),
                        Or(start[j] >= end[i] + tij,
                           start[i] >= end[j] + tji)))

# Objectives:
# 1) Maximize number of people met
count_met = Sum([If(meet[i], IntVal(1), IntVal(0)) for i in range(n)])
opt.maximize(count_met)

# 2) As a mild tie-breaker, minimize the sum of meeting start times (encourage earlier schedule / less idle)
#    We negate sums to use maximize (Z3 Optimize supports minimize, but we'll keep a consistent direction)
opt.minimize(Sum([If(meet[i], start[i], IntVal(0)) for i in range(n)]))

# Solve
if opt.check() != sat:
    print(json.dumps({"itinerary": []}, indent=2))
    exit(0)

model = opt.model()

# Extract chosen meetings
selected = []
for i, p in enumerate(people):
    if is_true(model.eval(meet[i])):
        s = model.eval(start[i]).as_long()
        e = model.eval(end[i]).as_long()
        selected.append({
            "person": p["name"],
            "location": p["location"],
            "start": s,
            "end": e
        })

# Sort by start time
selected.sort(key=lambda x: x["start"])

# Build JSON itinerary
itinerary = []
for item in selected:
    itinerary.append({
        "action": "meet",
        "location": item["location"],
        "person": item["person"],
        "start_time": fmt_time(item["start"]),
        "end_time": fmt_time(item["end"])
    })

print(json.dumps({"itinerary": itinerary}, indent=2))