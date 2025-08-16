# Requires: z3-solver (pip install z3-solver)
from z3 import *
import json

def minutes(h, m):
    return h * 60 + m

def to_hhmm(t):
    h = t // 60
    m = t % 60
    return f"{h:02d}:{m:02d}"

# Neighborhoods
N = [
    "Mission District",
    "Alamo Square",
    "Presidio",
    "Russian Hill",
    "North Beach",
    "Golden Gate Park",
    "Richmond District",
    "Embarcadero",
    "Financial District",
    "Marina District",
]

# Directed travel times in minutes (as provided)
T = {}
def set_time(a, b, t):
    T[(a, b)] = t

# Mission District row
set_time("Mission District", "Alamo Square", 11)
set_time("Mission District", "Presidio", 25)
set_time("Mission District", "Russian Hill", 15)
set_time("Mission District", "North Beach", 17)
set_time("Mission District", "Golden Gate Park", 17)
set_time("Mission District", "Richmond District", 20)
set_time("Mission District", "Embarcadero", 19)
set_time("Mission District", "Financial District", 15)
set_time("Mission District", "Marina District", 19)

# Alamo Square row
set_time("Alamo Square", "Mission District", 10)
set_time("Alamo Square", "Presidio", 17)
set_time("Alamo Square", "Russian Hill", 13)
set_time("Alamo Square", "North Beach", 15)
set_time("Alamo Square", "Golden Gate Park", 9)
set_time("Alamo Square", "Richmond District", 11)
set_time("Alamo Square", "Embarcadero", 16)
set_time("Alamo Square", "Financial District", 17)
set_time("Alamo Square", "Marina District", 15)

# Presidio row
set_time("Presidio", "Mission District", 26)
set_time("Presidio", "Alamo Square", 19)
set_time("Presidio", "Russian Hill", 14)
set_time("Presidio", "North Beach", 18)
set_time("Presidio", "Golden Gate Park", 12)
set_time("Presidio", "Richmond District", 7)
set_time("Presidio", "Embarcadero", 20)
set_time("Presidio", "Financial District", 23)
set_time("Presidio", "Marina District", 11)

# Russian Hill row
set_time("Russian Hill", "Mission District", 16)
set_time("Russian Hill", "Alamo Square", 15)
set_time("Russian Hill", "Presidio", 14)
set_time("Russian Hill", "North Beach", 5)
set_time("Russian Hill", "Golden Gate Park", 21)
set_time("Russian Hill", "Richmond District", 14)
set_time("Russian Hill", "Embarcadero", 8)
set_time("Russian Hill", "Financial District", 11)
set_time("Russian Hill", "Marina District", 7)

# North Beach row
set_time("North Beach", "Mission District", 18)
set_time("North Beach", "Alamo Square", 16)
set_time("North Beach", "Presidio", 17)
set_time("North Beach", "Russian Hill", 4)
set_time("North Beach", "Golden Gate Park", 22)
set_time("North Beach", "Richmond District", 18)
set_time("North Beach", "Embarcadero", 6)
set_time("North Beach", "Financial District", 8)
set_time("North Beach", "Marina District", 9)

# Golden Gate Park row
set_time("Golden Gate Park", "Mission District", 17)
set_time("Golden Gate Park", "Alamo Square", 9)
set_time("Golden Gate Park", "Presidio", 11)
set_time("Golden Gate Park", "Russian Hill", 19)
set_time("Golden Gate Park", "North Beach", 23)
set_time("Golden Gate Park", "Richmond District", 7)
set_time("Golden Gate Park", "Embarcadero", 25)
set_time("Golden Gate Park", "Financial District", 26)
set_time("Golden Gate Park", "Marina District", 16)

# Richmond District row
set_time("Richmond District", "Mission District", 20)
set_time("Richmond District", "Alamo Square", 13)
set_time("Richmond District", "Presidio", 7)
set_time("Richmond District", "Russian Hill", 13)
set_time("Richmond District", "North Beach", 17)
set_time("Richmond District", "Golden Gate Park", 9)
set_time("Richmond District", "Embarcadero", 19)
set_time("Richmond District", "Financial District", 22)
set_time("Richmond District", "Marina District", 9)

# Embarcadero row
set_time("Embarcadero", "Mission District", 20)
set_time("Embarcadero", "Alamo Square", 19)
set_time("Embarcadero", "Presidio", 20)
set_time("Embarcadero", "Russian Hill", 8)
set_time("Embarcadero", "North Beach", 5)
set_time("Embarcadero", "Golden Gate Park", 25)
set_time("Embarcadero", "Richmond District", 21)
set_time("Embarcadero", "Financial District", 5)
set_time("Embarcadero", "Marina District", 12)

# Financial District row
set_time("Financial District", "Mission District", 17)
set_time("Financial District", "Alamo Square", 17)
set_time("Financial District", "Presidio", 22)
set_time("Financial District", "Russian Hill", 11)
set_time("Financial District", "North Beach", 7)
set_time("Financial District", "Golden Gate Park", 23)
set_time("Financial District", "Richmond District", 21)
set_time("Financial District", "Embarcadero", 4)
set_time("Financial District", "Marina District", 15)

# Marina District row
set_time("Marina District", "Mission District", 20)
set_time("Marina District", "Alamo Square", 15)
set_time("Marina District", "Presidio", 10)
set_time("Marina District", "Russian Hill", 8)
set_time("Marina District", "North Beach", 11)
set_time("Marina District", "Golden Gate Park", 18)
set_time("Marina District", "Richmond District", 11)
set_time("Marina District", "Embarcadero", 14)
set_time("Marina District", "Financial District", 17)

# Friend data
friends = [
    {"name": "Laura",     "loc": "Alamo Square",      "avail_start": minutes(14,30), "avail_end": minutes(16,15), "min_dur": 75},
    {"name": "Brian",     "loc": "Presidio",          "avail_start": minutes(10,15), "avail_end": minutes(17, 0), "min_dur": 30},
    {"name": "Karen",     "loc": "Russian Hill",      "avail_start": minutes(18, 0), "avail_end": minutes(20,15), "min_dur": 90},
    {"name": "Stephanie", "loc": "North Beach",       "avail_start": minutes(10,15), "avail_end": minutes(16, 0), "min_dur": 75},
    {"name": "Helen",     "loc": "Golden Gate Park",  "avail_start": minutes(11,30), "avail_end": minutes(21,45), "min_dur": 120},
    {"name": "Sandra",    "loc": "Richmond District", "avail_start": minutes( 8, 0), "avail_end": minutes(15,15), "min_dur": 30},
    {"name": "Mary",      "loc": "Embarcadero",       "avail_start": minutes(16,45), "avail_end": minutes(18,45), "min_dur": 120},
    {"name": "Deborah",   "loc": "Financial District","avail_start": minutes(19, 0), "avail_end": minutes(20,45), "min_dur": 105},
    {"name": "Elizabeth", "loc": "Marina District",   "avail_start": minutes( 8,30), "avail_end": minutes(13,15), "min_dur": 105},
]

idx = {f["name"]: i for i, f in enumerate(friends)}
n = len(friends)

# Helper: travel time between two friends
def travel_time(i, j):
    return T[(friends[i]["loc"], friends[j]["loc"])]

def travel_from_mission(i):
    return T[("Mission District", friends[i]["loc"])]

origin_time = minutes(9,0)

# Z3 variables
opt = Optimize()

meet = [Bool(f"meet_{i}") for i in range(n)]
start = [Int(f"start_{i}") for i in range(n)]
end   = [Int(f"end_{i}") for i in range(n)]
order = [[BoolVal(False) if i == j else Bool(f"o_{i}_{j}") for j in range(n)] for i in range(n)]

# Domains for times
for i in range(n):
    opt.add(start[i] >= 0, start[i] <= 24*60)
    opt.add(end[i]   >= 0, end[i]   <= 24*60)
    opt.add(end[i] >= start[i])  # general consistency

# Meeting window and duration constraints
for i in range(n):
    a0 = friends[i]["avail_start"]
    a1 = friends[i]["avail_end"]
    mind = friends[i]["min_dur"]
    opt.add(Implies(meet[i], start[i] >= a0))
    opt.add(Implies(meet[i], end[i]   <= a1))
    opt.add(Implies(meet[i], end[i] - start[i] >= mind))
    # If not meeting, collapse the interval
    opt.add(Implies(Not(meet[i]), end[i] == start[i]))

# Order consistency and travel-time separation
for i in range(n):
    for j in range(n):
        if i == j:
            continue
        # Order implies both are met
        opt.add(Implies(order[i][j], And(meet[i], meet[j])))
        # If both are met, exactly one of order[i][j] or order[j][i] is true
        opt.add(Implies(And(meet[i], meet[j]), Xor(order[i][j], order[j][i])))
        # Travel-time separation
        tij = travel_time(i, j)
        opt.add(Implies(order[i][j], start[j] >= end[i] + tij))

# First-meeting-from-origin constraint using big-M relaxation if there is at least one predecessor
M = 100000
for i in range(n):
    num_preds = Sum([If(order[j][i], 1, 0) for j in range(n) if j != i])
    opt.add(Implies(meet[i], start[i] >= origin_time + travel_from_mission(i) - M * num_preds))

# Objective 1: maximize number of friends met
total_met = Sum([If(meet[i], 1, 0) for i in range(n)])
opt.maximize(total_met)

# Objective 2: maximize total meeting time (lexicographic, secondary)
total_time = Sum([If(meet[i], end[i] - start[i], 0) for i in range(n)])
opt.maximize(total_time)

# Solve
if opt.check() != sat:
    # If unsat (shouldn't happen for this instance), output empty itinerary
    print(json.dumps({"itinerary": []}))
else:
    m = opt.model()
    schedule = []
    for i in range(n):
        if is_true(m.evaluate(meet[i])):
            st = m.evaluate(start[i]).as_long()
            en = m.evaluate(end[i]).as_long()
            schedule.append({
                "person": friends[i]["name"],
                "start": st,
                "end": en
            })
    # Sort by start time
    schedule.sort(key=lambda x: x["start"])
    # Format output
    itinerary = []
    for s in schedule:
        itinerary.append({
            "action": "meet",
            "person": s["person"],
            "start_time": to_hhmm(s["start"]),
            "end_time": to_hhmm(s["end"])
        })
    print(json.dumps({"itinerary": itinerary}))