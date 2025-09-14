# SOLUTION:
# Compute an optimal meeting schedule using Z3 SMT solver
# The script builds an SMT model with travel and availability constraints,
# maximizes the number of friends met, and outputs a JSON itinerary.

from z3 import *
import json

def time_to_min(tstr):
    # Not used; times are embedded as minutes directly
    return 0

def min_to_str(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

# Locations
RH = "Russian Hill"
locations = [
    "Russian Hill", "Sunset District", "Union Square", "Nob Hill", "Marina District",
    "Richmond District", "Financial District", "Embarcadero", "The Castro",
    "Alamo Square", "Presidio"
]

# Travel times in minutes (asymmetric), as provided
T = {
    "Russian Hill": {
        "Sunset District": 23, "Union Square": 10, "Nob Hill": 5, "Marina District": 7,
        "Richmond District": 14, "Financial District": 11, "Embarcadero": 8,
        "The Castro": 21, "Alamo Square": 15, "Presidio": 14
    },
    "Sunset District": {
        "Russian Hill": 24, "Union Square": 30, "Nob Hill": 27, "Marina District": 21,
        "Richmond District": 12, "Financial District": 30, "Embarcadero": 30,
        "The Castro": 17, "Alamo Square": 17, "Presidio": 16
    },
    "Union Square": {
        "Russian Hill": 13, "Sunset District": 27, "Nob Hill": 9, "Marina District": 18,
        "Richmond District": 20, "Financial District": 9, "Embarcadero": 11,
        "The Castro": 17, "Alamo Square": 15, "Presidio": 24
    },
    "Nob Hill": {
        "Russian Hill": 5, "Sunset District": 24, "Union Square": 7, "Marina District": 11,
        "Richmond District": 14, "Financial District": 9, "Embarcadero": 9,
        "The Castro": 17, "Alamo Square": 11, "Presidio": 17
    },
    "Marina District": {
        "Russian Hill": 8, "Sunset District": 19, "Union Square": 16, "Nob Hill": 12,
        "Richmond District": 11, "Financial District": 17, "Embarcadero": 14,
        "The Castro": 22, "Alamo Square": 15, "Presidio": 10
    },
    "Richmond District": {
        "Russian Hill": 13, "Sunset District": 11, "Union Square": 21, "Nob Hill": 17,
        "Marina District": 9, "Financial District": 22, "Embarcadero": 19,
        "The Castro": 16, "Alamo Square": 13, "Presidio": 7
    },
    "Financial District": {
        "Russian Hill": 11, "Sunset District": 30, "Union Square": 9, "Nob Hill": 8,
        "Marina District": 15, "Richmond District": 21, "Embarcadero": 4,
        "The Castro": 20, "Alamo Square": 17, "Presidio": 22
    },
    "Embarcadero": {
        "Russian Hill": 8, "Sunset District": 30, "Union Square": 10, "Nob Hill": 10,
        "Marina District": 12, "Richmond District": 21, "Financial District": 5,
        "The Castro": 25, "Alamo Square": 19, "Presidio": 20
    },
    "The Castro": {
        "Russian Hill": 18, "Sunset District": 17, "Union Square": 19, "Nob Hill": 16,
        "Marina District": 21, "Richmond District": 16, "Financial District": 21,
        "Embarcadero": 22, "Alamo Square": 8, "Presidio": 20
    },
    "Alamo Square": {
        "Russian Hill": 13, "Sunset District": 16, "Union Square": 14, "Nob Hill": 11,
        "Marina District": 15, "Richmond District": 11, "Financial District": 17,
        "Embarcadero": 16, "The Castro": 8, "Presidio": 17
    },
    "Presidio": {
        "Russian Hill": 14, "Sunset District": 15, "Union Square": 22, "Nob Hill": 18,
        "Marina District": 11, "Richmond District": 7, "Financial District": 23,
        "Embarcadero": 20, "The Castro": 21, "Alamo Square": 19
    }
}

# Friends data: location, availability window [start, end], minimum duration
# Times in minutes from midnight
def hm(h, m): return h*60 + m

friends = {
    "David":    {"location": "Sunset District",     "start": hm(9,15),  "end": hm(22,0),  "dur": 15},
    "Kenneth":  {"location": "Union Square",        "start": hm(21,15), "end": hm(21,45), "dur": 15},
    "Patricia": {"location": "Nob Hill",            "start": hm(15,0),  "end": hm(19,15), "dur": 120},
    "Mary":     {"location": "Marina District",     "start": hm(14,45), "end": hm(16,45), "dur": 45},
    "Charles":  {"location": "Richmond District",   "start": hm(17,15), "end": hm(21,0),  "dur": 15},
    "Joshua":   {"location": "Financial District",  "start": hm(14,30), "end": hm(17,15), "dur": 90},
    "Ronald":   {"location": "Embarcadero",         "start": hm(18,15), "end": hm(20,45), "dur": 30},
    "George":   {"location": "The Castro",          "start": hm(14,15), "end": hm(19,0),  "dur": 105},
    "Kimberly": {"location": "Alamo Square",        "start": hm(9,0),   "end": hm(14,30), "dur": 105},
    "William":  {"location": "Presidio",            "start": hm(7,0),   "end": hm(12,45), "dur": 60},
}

people = list(friends.keys())

# SMT variables
meet = {p: Bool(f"meet_{p}") for p in people}
start = {p: Int(f"start_{p}") for p in people}
end = {p: Int(f"end_{p}") for p in people}

# Ordering variables between every pair
order = {}
for i in range(len(people)):
    for j in range(len(people)):
        if i == j: continue
        pi, pj = people[i], people[j]
        order[(pi,pj)] = Bool(f"ord_{pi}_{pj}")

# Start-from-origin (Russian Hill at 9:00) precedence flags
start_from_origin = {p: Bool(f"from_start_{p}") for p in people}

opt = Optimize()

# Helper: Bool to Int
def b2i(b):
    return If(b, 1, 0)

# Domain constraints
for p in people:
    # Non-negativity and within a reasonable day window
    opt.add(start[p] >= 0, end[p] >= 0, end[p] == start[p] + friends[p]["dur"])
    # Availability if meeting
    s = friends[p]["start"]
    e = friends[p]["end"]
    opt.add(Implies(meet[p], And(start[p] >= s, end[p] <= e)))
    # If not meeting, start/end can be anything; but keep end >= start
    opt.add(Implies(Not(meet[p]), start[p] <= end[p]))

# Pairwise non-overlap with travel and total order if both met
for i in range(len(people)):
    for j in range(i+1, len(people)):
        pi, pj = people[i], people[j]
        li = friends[pi]["location"]
        lj = friends[pj]["location"]
        # Create both direction order variables
        oij = order[(pi,pj)]
        oji = order[(pj,pi)]
        # If we set an order, both meetings must occur
        opt.add(Implies(oij, And(meet[pi], meet[pj])))
        opt.add(Implies(oji, And(meet[pi], meet[pj])))
        # Travel feasibility
        tij = T[li][lj]
        tji = T[lj][li]
        opt.add(Implies(oij, end[pi] + tij <= start[pj]))
        opt.add(Implies(oji, end[pj] + tji <= start[pi]))
        # At least one order must hold if both meetings occur
        opt.add(b2i(oij) + b2i(oji) >= b2i(meet[pi]) + b2i(meet[pj]) - 1)
        # Can't have both directions simultaneously
        opt.add(Not(And(oij, oji)))

# Start from Russian Hill at 9:00
day_start = hm(9,0)
for p in people:
    loc = friends[p]["location"]
    # If we choose this as directly after origin, must respect travel from origin
    opt.add(Implies(start_from_origin[p], meet[p]))
    opt.add(Implies(start_from_origin[p], day_start + T[RH][loc] <= start[p]))
    # Every met meeting must either be after the origin or after another meeting
    preds = [order[(q,p)] for q in people if q != p]
    opt.add(Implies(meet[p], Or(start_from_origin[p], Or(preds) if preds else False)))

# Objective: maximize number of friends met
opt.maximize(Sum([b2i(meet[p]) for p in people]))

# Secondary objective: among equal counts, minimize total start times (prefer earlier schedule)
opt.minimize(Sum([If(meet[p], start[p], 0) for p in people]))

# Solve
if opt.check() != sat:
    print(json.dumps({"itinerary": []}))
    exit(0)

m = opt.model()

# Build itinerary
events = []
for p in people:
    if is_true(m.eval(meet[p])):
        st = m.eval(start[p]).as_long()
        en = m.eval(end[p]).as_long()
        events.append({
            "action": "meet",
            "location": friends[p]["location"],
            "person": p,
            "start_time": min_to_str(st),
            "end_time": min_to_str(en)
        })

# Sort by start_time
events.sort(key=lambda x: int(x["start_time"].split(":")[0])*60 + int(x["start_time"].split(":")[1]))

print(json.dumps({"itinerary": events}, indent=2))