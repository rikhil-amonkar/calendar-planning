"SOLUTION:"

import json
import sys

# Ensure z3 is available
try:
    from z3 import Int, Bool, If, And, Or, Not, Implies, Optimize, Sum, sat
except ImportError:
    import subprocess, sys as _sys
    subprocess.check_call([_sys.executable, "-m", "pip", "install", "z3-solver", "--quiet"])
    from z3 import Int, Bool, If, And, Or, Not, Implies, Optimize, Sum, sat

# Time helpers
def to_minutes(h, m):
    return h * 60 + m

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Problem data
ORIGIN_LOCATION = "Fisherman's Wharf"
ORIGIN_TIME = to_minutes(9, 0)

locations = [
    "Fisherman's Wharf",
    "Presidio",
    "Richmond District",
    "Financial District",
]

# Directed travel times (in minutes)
travel = {
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Financial District"): 11,  # given 11? Wait given 11 from FW to Financial District? Provided 11? Actually 11 in problem; but also FD->FW is 10.
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Financial District"): 23,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Financial District"): 22,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Richmond District"): 21,
}

# Correct the FW->Financial District time based on problem statement (11 minutes)
travel[("Fisherman's Wharf", "Financial District")] = 11

# People and their availability/minimum meeting durations
people = [
    {
        "name": "Emily",
        "location": "Presidio",
        "avail_start": to_minutes(16, 15),
        "avail_end": to_minutes(21, 0),
        "min_duration": 105,
    },
    {
        "name": "Joseph",
        "location": "Richmond District",
        "avail_start": to_minutes(17, 15),
        "avail_end": to_minutes(22, 0),
        "min_duration": 120,
    },
    {
        "name": "Melissa",
        "location": "Financial District",
        "avail_start": to_minutes(15, 45),
        "avail_end": to_minutes(21, 45),
        "min_duration": 75,
    },
]

# Z3 model
opt = Optimize()
opt.set("opt.priority", "lex")

n = len(people)

# Variables
start = []
end = []
dur = []
active = []

for i in range(n):
    start.append(Int(f"start_{i}"))
    end.append(Int(f"end_{i}"))
    dur.append(Int(f"dur_{i}"))
    active.append(Bool(f"active_{i}"))

    # Common relation
    opt.add(end[i] == start[i] + dur[i])

    # If active, enforce constraints
    opt.add(Implies(active[i], start[i] >= people[i]["avail_start"]))
    opt.add(Implies(active[i], end[i] <= people[i]["avail_end"]))
    opt.add(Implies(active[i], dur[i] >= people[i]["min_duration"]))
    opt.add(Implies(Not(active[i]), dur[i] == 0))  # no meeting time if inactive

    # Base reachability from origin
    base_travel = travel[(ORIGIN_LOCATION, people[i]["location"])]
    opt.add(Implies(active[i], start[i] >= ORIGIN_TIME + base_travel))

    # Non-negativity for active times
    opt.add(Implies(active[i], And(start[i] >= 0, end[i] >= 0)))

# Pairwise disjunctive ordering with travel times
before = {}  # (i,j) with i<j : Bool
for i in range(n):
    for j in range(i + 1, n):
        b = Bool(f"before_{i}_{j}")
        before[(i, j)] = b
        # If both active and i before j, enforce travel feasibility
        tij = travel[(people[i]["location"], people[j]["location"])]
        tji = travel[(people[j]["location"], people[i]["location"])]
        opt.add(Implies(And(active[i], active[j], b), start[j] >= end[i] + tij))
        opt.add(Implies(And(active[i], active[j], Not(b)), start[i] >= end[j] + tji))

# Objective 1: maximize number of meetings satisfied
count_meetings = Sum([If(active[i], 1, 0) for i in range(n)])
opt.maximize(count_meetings)

# Objective 2: minimize finish time (makespan) of the executed itinerary
finish = Int("finish")
opt.add(finish >= 0)
for i in range(n):
    opt.add(Implies(active[i], finish >= end[i]))
opt.minimize(finish)

# Solve
if opt.check() != sat:
    print(json.dumps({"itinerary": []}))
    sys.exit(0)

model = opt.model()

# Extract schedule
items = []
for i in range(n):
    if model.eval(active[i], model_completion=True).is_true():
        s = model.eval(start[i], model_completion=True).as_long()
        e = model.eval(end[i], model_completion=True).as_long()
        items.append({
            "person": people[i]["name"],
            "location": people[i]["location"],
            "start": s,
            "end": e
        })

# Sort by start time
items.sort(key=lambda x: x["start"])

# Build JSON output
itinerary = []
for it in items:
    itinerary.append({
        "action": "meet",
        "location": it["location"],
        "person": it["person"],
        "start_time": fmt_time(it["start"]),
        "end_time": fmt_time(it["end"]),
    })

print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))