import json
from z3 import *

def minutes(h, m):
    return h * 60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Data
start_location = "Embarcadero"
arrival_time = minutes(9, 0)  # 9:00

people = [
    {"name": "Kenneth", "location": "Richmond District", "window": (minutes(21, 15), minutes(22, 0)), "min_dur": 30},
    {"name": "Lisa", "location": "Union Square", "window": (minutes(9, 0), minutes(16, 30)), "min_dur": 45},
    {"name": "Joshua", "location": "Financial District", "window": (minutes(12, 0), minutes(15, 15)), "min_dur": 15},
    {"name": "Nancy", "location": "Pacific Heights", "window": (minutes(8, 0), minutes(11, 30)), "min_dur": 90},
    {"name": "Andrew", "location": "Nob Hill", "window": (minutes(11, 30), minutes(20, 15)), "min_dur": 60},
    {"name": "John", "location": "Bayview", "window": (minutes(16, 45), minutes(21, 30)), "min_dur": 75},
]

# Travel times (minutes), directed
travel = {
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Pacific Heights"): 11,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Bayview"): 21,

    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Bayview"): 26,

    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Bayview"): 15,

    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Bayview"): 19,

    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Bayview"): 22,

    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Bayview"): 19,

    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Union Square"): 17,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Nob Hill"): 20,
}

# Z3 setup
opt = Optimize()

# Variables per person
meet = {}
start = {}
dur = {}
end = {}

for p in people:
    name = p["name"]
    meet[name] = Bool(f"meet_{name}")
    start[name] = Int(f"start_{name}")
    dur[name] = Int(f"dur_{name}")
    end[name] = Int(f"end_{name}")

    loc = p["location"]
    w_start, w_end = p["window"]
    min_dur = p["min_dur"]

    # domain bounds to keep numbers reasonable
    opt.add(start[name] >= 0, start[name] <= minutes(23,59))
    opt.add(dur[name] >= 0, dur[name] <= minutes(23,59))
    opt.add(end[name] >= 0, end[name] <= minutes(23,59))
    opt.add(end[name] == start[name] + dur[name])

    # If meeting occurs, respect window, duration, and initial travel feasibility
    opt.add(Implies(meet[name], And(
        start[name] >= w_start,
        end[name] <= w_end,
        dur[name] >= min_dur,
        start[name] >= arrival_time + travel[(start_location, loc)]
    )))
    # If not meeting, zero duration and end aligned to start (arbitrary start allowed)
    opt.add(Implies(Not(meet[name]), And(dur[name] == 0, end[name] == start[name])))

# Pairwise non-overlap with travel time between locations
for i in range(len(people)):
    for j in range(i + 1, len(people)):
        pi = people[i]["name"]
        pj = people[j]["name"]
        li = people[i]["location"]
        lj = people[j]["location"]
        tij = travel[(li, lj)]
        tji = travel[(lj, li)]
        # If both meetings happen, enforce an order with travel time
        opt.add(Implies(And(meet[pi], meet[pj]),
                        Or(start[pj] >= end[pi] + tij,
                           start[pi] >= end[pj] + tji)))

# Objectives: maximize number of people met, then maximize total meeting time
count_met = Sum([If(meet[p["name"]], 1, 0) for p in people])
total_minutes = Sum([dur[p["name"]] for p in people])
opt.maximize(count_met)
opt.maximize(total_minutes)

# Solve
if opt.check() != sat:
    print(json.dumps({"itinerary": []}))
    exit(0)

m = opt.model()

# Build itinerary
entries = []
for p in people:
    name = p["name"]
    if m.evaluate(meet[name], model_completion=True):
        s = m.evaluate(start[name], model_completion=True).as_long()
        e = m.evaluate(end[name], model_completion=True).as_long()
        entries.append({
            "action": "meet",
            "location": p["location"],
            "person": name,
            "start_time": fmt_time(s),
            "end_time": fmt_time(e),
        })

# Sort by start time
entries.sort(key=lambda x: (int(x["start_time"].split(":")[0]) * 60 + int(x["start_time"].split(":")[1])))

# Output JSON
result = {"itinerary": entries}
print(json.dumps(result, ensure_ascii=False))