import json
from z3 import *

def minutes(h, m):
    return h * 60 + m

def min_to_str(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Locations
locs = [
    "Financial District",
    "Fisherman's Wharf",
    "Presidio",
    "Bayview",
    "Haight-Ashbury",
    "Russian Hill",
    "The Castro",
    "Marina District",
    "Richmond District",
    "Union Square",
    "Sunset District",
]

# Travel times (minutes), directional
travel = {
    "Financial District": {
        "Fisherman's Wharf": 10,
        "Presidio": 22,
        "Bayview": 19,
        "Haight-Ashbury": 19,
        "Russian Hill": 11,
        "The Castro": 20,
        "Marina District": 15,
        "Richmond District": 21,
        "Union Square": 9,
        "Sunset District": 30,
    },
    "Fisherman's Wharf": {
        "Financial District": 11,
        "Presidio": 17,
        "Bayview": 26,
        "Haight-Ashbury": 22,
        "Russian Hill": 7,
        "The Castro": 27,
        "Marina District": 9,
        "Richmond District": 18,
        "Union Square": 13,
        "Sunset District": 27,
    },
    "Presidio": {
        "Financial District": 23,
        "Fisherman's Wharf": 19,
        "Bayview": 31,
        "Haight-Ashbury": 15,
        "Russian Hill": 14,
        "The Castro": 21,
        "Marina District": 11,
        "Richmond District": 7,
        "Union Square": 22,
        "Sunset District": 15,
    },
    "Bayview": {
        "Financial District": 19,
        "Fisherman's Wharf": 25,
        "Presidio": 32,
        "Haight-Ashbury": 19,
        "Russian Hill": 23,
        "The Castro": 19,
        "Marina District": 27,
        "Richmond District": 25,
        "Union Square": 18,
        "Sunset District": 23,
    },
    "Haight-Ashbury": {
        "Financial District": 21,
        "Fisherman's Wharf": 23,
        "Presidio": 15,
        "Bayview": 18,
        "Russian Hill": 17,
        "The Castro": 6,
        "Marina District": 17,
        "Richmond District": 10,
        "Union Square": 19,
        "Sunset District": 15,
    },
    "Russian Hill": {
        "Financial District": 11,
        "Fisherman's Wharf": 7,
        "Presidio": 14,
        "Bayview": 23,
        "Haight-Ashbury": 17,
        "The Castro": 21,
        "Marina District": 7,
        "Richmond District": 14,
        "Union Square": 10,
        "Sunset District": 23,
    },
    "The Castro": {
        "Financial District": 21,
        "Fisherman's Wharf": 24,
        "Presidio": 20,
        "Bayview": 19,
        "Haight-Ashbury": 6,
        "Russian Hill": 18,
        "Marina District": 21,
        "Richmond District": 16,
        "Union Square": 19,
        "Sunset District": 17,
    },
    "Marina District": {
        "Financial District": 17,
        "Fisherman's Wharf": 10,
        "Presidio": 10,
        "Bayview": 27,
        "Haight-Ashbury": 16,
        "Russian Hill": 8,
        "The Castro": 22,
        "Richmond District": 11,
        "Union Square": 16,
        "Sunset District": 19,
    },
    "Richmond District": {
        "Financial District": 22,
        "Fisherman's Wharf": 18,
        "Presidio": 7,
        "Bayview": 27,
        "Haight-Ashbury": 10,
        "Russian Hill": 13,
        "The Castro": 16,
        "Marina District": 9,
        "Union Square": 21,
        "Sunset District": 11,
    },
    "Union Square": {
        "Financial District": 9,
        "Fisherman's Wharf": 15,
        "Presidio": 24,
        "Bayview": 15,
        "Haight-Ashbury": 18,
        "Russian Hill": 13,
        "The Castro": 17,
        "Marina District": 18,
        "Richmond District": 20,
        "Sunset District": 27,
    },
    "Sunset District": {
        "Financial District": 30,
        "Fisherman's Wharf": 29,
        "Presidio": 16,
        "Bayview": 22,
        "Haight-Ashbury": 15,
        "Russian Hill": 24,
        "The Castro": 17,
        "Marina District": 21,
        "Richmond District": 12,
        "Union Square": 30,
    },
}

# People and their constraints
people = [
    {"name": "Mark", "location": "Fisherman's Wharf", "avail_start": minutes(8,15), "avail_end": minutes(10,0), "duration": 30},
    {"name": "Stephanie", "location": "Presidio", "avail_start": minutes(12,15), "avail_end": minutes(15,0), "duration": 75},
    {"name": "Betty", "location": "Bayview", "avail_start": minutes(7,15), "avail_end": minutes(20,30), "duration": 15},
    {"name": "Lisa", "location": "Haight-Ashbury", "avail_start": minutes(15,30), "avail_end": minutes(18,30), "duration": 45},
    {"name": "William", "location": "Russian Hill", "avail_start": minutes(18,45), "avail_end": minutes(20,0), "duration": 60},
    {"name": "Brian", "location": "The Castro", "avail_start": minutes(9,15), "avail_end": minutes(13,15), "duration": 30},
    {"name": "Joseph", "location": "Marina District", "avail_start": minutes(10,45), "avail_end": minutes(15,0), "duration": 90},
    {"name": "Ashley", "location": "Richmond District", "avail_start": minutes(9,45), "avail_end": minutes(11,15), "duration": 45},
    {"name": "Patricia", "location": "Union Square", "avail_start": minutes(16,30), "avail_end": minutes(20,0), "duration": 120},
    {"name": "Karen", "location": "Sunset District", "avail_start": minutes(16,30), "avail_end": minutes(22,0), "duration": 105},
]

N = len(people)
start_loc = "Financial District"
start_time = minutes(9, 0)

# Z3 variables
start_vars = [Int(f"start_{i}") for i in range(N)]
rank_vars = [Int(f"rank_{i}") for i in range(N)]
sel_vars = [Bool(f"sel_{i}") for i in range(N)]

opt = Optimize()
opt.set(priority='lex')

# Bounds
for i in range(N):
    # Times within day bounds
    opt.add(start_vars[i] >= 0, start_vars[i] <= 24*60)
    opt.add(rank_vars[i] >= 0, rank_vars[i] <= N-1)

# Selection implies availability and minimum duration end before window end
for i, p in enumerate(people):
    s = start_vars[i]
    dur = p["duration"]
    opt.add(Implies(sel_vars[i], And(
        s >= p["avail_start"],
        s + dur <= p["avail_end"],
    )))

# Distinct ranks among selected
for i in range(N):
    for j in range(i+1, N):
        opt.add(Implies(And(sel_vars[i], sel_vars[j]), rank_vars[i] != rank_vars[j]))

# Travel-time and sequencing constraints between all pairs
for i, pi in enumerate(people):
    for j, pj in enumerate(people):
        if i == j:
            continue
        # If i before j
        opt.add(Implies(And(sel_vars[i], sel_vars[j], rank_vars[i] < rank_vars[j]),
                        start_vars[j] >= start_vars[i] + pi["duration"] + travel[pi["location"]][pj["location"]]))

# Constraint for the first selected meeting: must account for travel from start location/time
for i, p in enumerate(people):
    is_first = And(sel_vars[i], And([Implies(sel_vars[j], rank_vars[i] < rank_vars[j]) for j in range(N) if j != i]))
    opt.add(Implies(is_first, start_vars[i] >= start_time + travel[start_loc][p["location"]]))

# Objective: maximize number of meetings, then maximize total meeting minutes (weights favor longer meetings)
count_meetings = Sum([If(sel_vars[i], 1, 0) for i in range(N)])
total_minutes = Sum([If(sel_vars[i], people[i]["duration"], 0) for i in range(N)])
opt.maximize(count_meetings)
opt.maximize(total_minutes)

if opt.check() != sat:
    print(json.dumps({"itinerary": []}))
else:
    m = opt.model()
    selected = []
    for i, p in enumerate(people):
        if is_true(m.eval(sel_vars[i])):
            st = m.eval(start_vars[i]).as_long()
            en = st + p["duration"]
            selected.append({
                "person": p["name"],
                "location": p["location"],
                "start": st,
                "end": en,
                "rank": m.eval(rank_vars[i]).as_long()
            })
    # Sort by start time (or rank)
    selected.sort(key=lambda x: x["start"])
    itinerary = []
    for item in selected:
        itinerary.append({
            "action": "meet",
            "location": item["location"],
            "person": item["person"],
            "start_time": min_to_str(item["start"]),
            "end_time": min_to_str(item["end"])
        })
    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))