from z3 import *
import json
import re

def min_to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Locations
locations = [
    "Marina District",
    "Richmond District",
    "Union Square",
    "Nob Hill",
    "Fisherman's Wharf",
    "Golden Gate Park",
    "Embarcadero",
    "Financial District",
    "North Beach",
    "Presidio",
]

# Travel times (minutes) as given
travel = {
    "Marina District": {
        "Richmond District": 11, "Union Square": 16, "Nob Hill": 12, "Fisherman's Wharf": 10,
        "Golden Gate Park": 18, "Embarcadero": 14, "Financial District": 17, "North Beach": 11, "Presidio": 10
    },
    "Richmond District": {
        "Marina District": 9, "Union Square": 21, "Nob Hill": 17, "Fisherman's Wharf": 18,
        "Golden Gate Park": 9, "Embarcadero": 19, "Financial District": 22, "North Beach": 17, "Presidio": 7
    },
    "Union Square": {
        "Marina District": 18, "Richmond District": 20, "Nob Hill": 9, "Fisherman's Wharf": 15,
        "Golden Gate Park": 22, "Embarcadero": 11, "Financial District": 9, "North Beach": 10, "Presidio": 24
    },
    "Nob Hill": {
        "Marina District": 11, "Richmond District": 14, "Union Square": 7, "Fisherman's Wharf": 10,
        "Golden Gate Park": 17, "Embarcadero": 9, "Financial District": 9, "North Beach": 8, "Presidio": 17
    },
    "Fisherman's Wharf": {
        "Marina District": 9, "Richmond District": 18, "Union Square": 13, "Nob Hill": 11,
        "Golden Gate Park": 25, "Embarcadero": 8, "Financial District": 11, "North Beach": 6, "Presidio": 17
    },
    "Golden Gate Park": {
        "Marina District": 16, "Richmond District": 7, "Union Square": 22, "Nob Hill": 20,
        "Fisherman's Wharf": 24, "Embarcadero": 25, "Financial District": 26, "North Beach": 23, "Presidio": 11
    },
    "Embarcadero": {
        "Marina District": 12, "Richmond District": 21, "Union Square": 10, "Nob Hill": 10,
        "Fisherman's Wharf": 6, "Golden Gate Park": 25, "Financial District": 5, "North Beach": 5, "Presidio": 20
    },
    "Financial District": {
        "Marina District": 15, "Richmond District": 21, "Union Square": 9, "Nob Hill": 8,
        "Fisherman's Wharf": 10, "Golden Gate Park": 23, "Embarcadero": 4, "North Beach": 7, "Presidio": 22
    },
    "North Beach": {
        "Marina District": 9, "Richmond District": 18, "Union Square": 7, "Nob Hill": 7,
        "Fisherman's Wharf": 5, "Golden Gate Park": 22, "Embarcadero": 6, "Financial District": 8, "Presidio": 17
    },
    "Presidio": {
        "Marina District": 11, "Richmond District": 7, "Union Square": 22, "Nob Hill": 18,
        "Fisherman's Wharf": 19, "Golden Gate Park": 12, "Embarcadero": 20, "Financial District": 23, "North Beach": 18
    },
}

def t(a, b):
    return travel[a][b]

# Friends with availability windows and minimum meeting durations
friends = [
    {"name": "Stephanie", "location": "Richmond District", "start": 16*60+15, "end": 21*60+30, "min_duration": 75},
    {"name": "William", "location": "Union Square", "start": 10*60+45, "end": 17*60+30, "min_duration": 45},
    {"name": "Elizabeth", "location": "Nob Hill", "start": 12*60+15, "end": 15*60+0, "min_duration": 105},
    {"name": "Joseph", "location": "Fisherman's Wharf", "start": 12*60+45, "end": 14*60+0, "min_duration": 75},
    {"name": "Anthony", "location": "Golden Gate Park", "start": 13*60+0, "end": 20*60+30, "min_duration": 75},
    {"name": "Barbara", "location": "Embarcadero", "start": 19*60+15, "end": 20*60+30, "min_duration": 75},
    {"name": "Carol", "location": "Financial District", "start": 11*60+45, "end": 16*60+15, "min_duration": 60},
    {"name": "Sandra", "location": "North Beach", "start": 10*60+0, "end": 12*60+30, "min_duration": 15},
    {"name": "Kenneth", "location": "Presidio", "start": 21*60+15, "end": 22*60+15, "min_duration": 45},
]

# Start info
start_location = "Marina District"
start_time = 9*60  # 9:00

# Create solver
opt = Optimize()

# Variables per friend
n = len(friends)
s_vars = []
e_vars = []
meet_bools = []
durations = []
locs = []
names = []
avail_starts = []
avail_ends = []

def clean_name(nm):
    return re.sub(r'[^A-Za-z0-9]+', '_', nm)

for i, f in enumerate(friends):
    nm = clean_name(f["name"])
    s = Int(f"s_{nm}")
    e = Int(f"e_{nm}")
    meet = Bool(f"meet_{nm}")
    s_vars.append(s)
    e_vars.append(e)
    meet_bools.append(meet)
    durations.append(f["min_duration"])
    locs.append(f["location"])
    names.append(f["name"])
    avail_starts.append(f["start"])
    avail_ends.append(f["end"])

    # Bounds
    opt.add(s >= 0, e >= 0, s <= 24*60, e <= 24*60)

    # Meeting window and duration if met
    opt.add(Implies(meet, And(
        s >= f["start"],
        e <= f["end"],
        e == s + f["min_duration"]
    )))
    # If not met, keep e == s to avoid spurious durations
    opt.add(Implies(Not(meet), e == s))

    # Must be reachable from start
    opt.add(Implies(meet, s >= start_time + t(start_location, f["location"])))

# Pairwise sequencing with travel time
before = {}
for i in range(n):
    for j in range(n):
        if i == j:
            continue
        b = Bool(f"before_{i}_{j}")
        before[(i, j)] = b

for i in range(n):
    for j in range(i+1, n):
        # If both meetings are chosen, one must precede the other
        opt.add(Implies(And(meet_bools[i], meet_bools[j]), Or(before[(i, j)], before[(j, i)])))
        # Cannot have both directions simultaneously
        opt.add(Not(And(before[(i, j)], before[(j, i)])))
        # Timing constraints with travel if i before j
        opt.add(Implies(And(meet_bools[i], meet_bools[j], before[(i, j)]),
                        s_vars[j] >= e_vars[i] + t(locs[i], locs[j])))
        # Timing constraints with travel if j before i
        opt.add(Implies(And(meet_bools[i], meet_bools[j], before[(j, i)]),
                        s_vars[i] >= e_vars[j] + t(locs[j], locs[i])))

# Objectives:
# 1) Maximize number of friends met
num_met = Sum([If(meet_bools[i], 1, 0) for i in range(n)])
opt.maximize(num_met)
# 2) Tie-breaker: maximize total meeting minutes
total_minutes = Sum([If(meet_bools[i], durations[i], 0) for i in range(n)])
opt.maximize(total_minutes)

# Solve
res = opt.check()
if res != sat and res != unknown:
    # Fallback: empty itinerary if unsat
    output = {"itinerary": []}
    print(json.dumps(output, indent=2))
else:
    m = opt.model()
    meetings = []
    for i in range(n):
        if is_true(m.evaluate(meet_bools[i])):
            start_i = m.evaluate(s_vars[i]).as_long()
            end_i = m.evaluate(e_vars[i]).as_long()
            meetings.append({
                "person": names[i],
                "location": locs[i],
                "start": start_i,
                "end": end_i
            })
    # Sort by start time
    meetings.sort(key=lambda x: x["start"])

    itinerary = []
    for mt in meetings:
        itinerary.append({
            "action": "meet",
            "location": mt["location"],
            "person": mt["person"],
            "start_time": min_to_str(mt["start"]),
            "end_time": min_to_str(mt["end"])
        })

    print(json.dumps({"itinerary": itinerary}, indent=2))