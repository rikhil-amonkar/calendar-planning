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
    "Nob Hill",
    "Richmond District",
    "Financial District",
    "North Beach",
    "The Castro",
    "Golden Gate Park"
]

# Travel times (in minutes)
travel = {
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Golden Gate Park"): 17,

    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Golden Gate Park"): 9,

    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "The Castro"): 23,
    ("Financial District", "Golden Gate Park"): 23,

    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "The Castro"): 22,
    ("North Beach", "Golden Gate Park"): 22,

    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Financial District"): 20,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Golden Gate Park"): 11,

    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "North Beach"): 24,
    ("Golden Gate Park", "The Castro"): 13,
}

# People and constraints
people = [
    {
        "name": "Emily",
        "location": "Richmond District",
        "avail_start": minutes(19, 0),
        "avail_end": minutes(21, 0),
        "min_duration": 15
    },
    {
        "name": "Margaret",
        "location": "Financial District",
        "avail_start": minutes(16, 30),
        "avail_end": minutes(20, 15),
        "min_duration": 75
    },
    {
        "name": "Ronald",
        "location": "North Beach",
        "avail_start": minutes(18, 30),
        "avail_end": minutes(19, 30),
        "min_duration": 45
    },
    {
        "name": "Deborah",
        "location": "The Castro",
        "avail_start": minutes(13, 45),
        "avail_end": minutes(21, 15),
        "min_duration": 90
    },
    {
        "name": "Jeffrey",
        "location": "Golden Gate Park",
        "avail_start": minutes(11, 15),
        "avail_end": minutes(14, 30),
        "min_duration": 120
    }
]

# Start parameters
start_location = "Nob Hill"
start_time = minutes(9, 0)

# Z3 model
opt = Optimize()
opt.set(priority='lex')

n = len(people)

start_vars = []
meet_bools = []
durations = []
locs = [p["location"] for p in people]

for p in people:
    var_name = "start_" + p["name"].replace(" ", "_")
    s = Int(var_name)
    m = Bool("meet_" + p["name"].replace(" ", "_"))
    start_vars.append(s)
    meet_bools.append(m)
    durations.append(p["min_duration"])
    # Bounds for time variables to keep domain reasonable
    opt.add(And(s >= 0, s <= minutes(23, 59)))

# Availability and base travel constraints
for i, p in enumerate(people):
    s = start_vars[i]
    m = meet_bools[i]
    dur = durations[i]
    avail_start = p["avail_start"]
    avail_end = p["avail_end"]
    # If meeting, respect availability window and minimal duration
    opt.add(Implies(m, And(s >= avail_start, s + dur <= avail_end)))
    # If meeting, must be reachable from the starting point
    base_travel = travel[(start_location, p["location"])]
    opt.add(Implies(m, s >= start_time + base_travel))

# Pairwise ordering and travel constraints
before = {}
for i in range(n):
    for j in range(i + 1, n):
        b = Bool(f"before_{i}_{j}")
        before[(i, j)] = b
        # If both meetings happen and i is before j
        opt.add(Implies(And(meet_bools[i], meet_bools[j], b),
                        start_vars[j] >= start_vars[i] + durations[i] + travel[(locs[i], locs[j])]))
        # If both meetings happen and j is before i
        opt.add(Implies(And(meet_bools[i], meet_bools[j], Not(b)),
                        start_vars[i] >= start_vars[j] + durations[j] + travel[(locs[j], locs[i])]))

# Objective: maximize the number of meetings
score = Sum([If(m, IntVal(1), IntVal(0)) for m in meet_bools])
opt.maximize(score)

# Secondary objective: minimize finishing time to prefer earlier feasible schedules
finish = Int("finish_time")
opt.add(And(finish >= 0, finish <= minutes(23, 59)))
for i in range(n):
    opt.add(Implies(meet_bools[i], finish >= start_vars[i] + durations[i]))
opt.minimize(finish)

# Solve
if opt.check() != sat:
    result = {"itinerary": []}
    print(json.dumps(result))
else:
    model = opt.model()
    itinerary = []
    for i, p in enumerate(people):
        if is_true(model[meet_bools[i]]):
            start_val = model[start_vars[i]].as_long()
            end_val = start_val + durations[i]
            itinerary.append({
                "action": "meet",
                "location": p["location"],
                "person": p["name"],
                "start_time": fmt_time(start_val),
                "end_time": fmt_time(end_val)
            })
    # Sort by start_time
    itinerary.sort(key=lambda x: (int(x["start_time"].split(":")[0]) * 60 + int(x["start_time"].split(":")[1])))
    print(json.dumps({"itinerary": itinerary}))