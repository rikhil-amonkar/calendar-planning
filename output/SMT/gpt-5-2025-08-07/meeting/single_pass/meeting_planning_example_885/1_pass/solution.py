# Requires: pip install z3-solver
from z3 import *
import json

# Time utilities
def hm(h, m=0):
    return h * 60 + m

def min_to_str(t):
    h = t // 60
    m = t % 60
    return f"{h:02d}:{m:02d}"

# Problem data
start_location = "Russian Hill"
start_time = hm(9, 0)

people = {
    "Mark":    {"loc": "Marina District",     "start": hm(18, 45), "end": hm(21, 0),  "min": 90},
    "Karen":   {"loc": "Financial District",  "start": hm(9, 30),  "end": hm(12, 45), "min": 90},
    "Barbara": {"loc": "Alamo Square",        "start": hm(10, 0),  "end": hm(19, 30), "min": 90},
    "Nancy":   {"loc": "Golden Gate Park",    "start": hm(16, 45), "end": hm(20, 0),  "min": 105},
    "David":   {"loc": "The Castro",          "start": hm(9, 0),   "end": hm(18, 0),  "min": 120},
    "Linda":   {"loc": "Bayview",             "start": hm(18, 15), "end": hm(19, 45), "min": 45},
    "Kevin":   {"loc": "Sunset District",     "start": hm(10, 0),  "end": hm(17, 45), "min": 120},
    "Matthew": {"loc": "Haight-Ashbury",      "start": hm(10, 15), "end": hm(15, 30), "min": 45},
    "Andrew":  {"loc": "Nob Hill",            "start": hm(11, 45), "end": hm(16, 45), "min": 105},
}

# Travel times (minutes)
travel = {
    "Russian Hill": {
        "Marina District": 7, "Financial District": 11, "Alamo Square": 15, "Golden Gate Park": 21,
        "The Castro": 21, "Bayview": 23, "Sunset District": 23, "Haight-Ashbury": 17, "Nob Hill": 5
    },
    "Marina District": {
        "Russian Hill": 8, "Financial District": 17, "Alamo Square": 15, "Golden Gate Park": 18,
        "The Castro": 22, "Bayview": 27, "Sunset District": 19, "Haight-Ashbury": 16, "Nob Hill": 12
    },
    "Financial District": {
        "Russian Hill": 11, "Marina District": 15, "Alamo Square": 17, "Golden Gate Park": 23,
        "The Castro": 20, "Bayview": 19, "Sunset District": 30, "Haight-Ashbury": 19, "Nob Hill": 8
    },
    "Alamo Square": {
        "Russian Hill": 13, "Marina District": 15, "Financial District": 17, "Golden Gate Park": 9,
        "The Castro": 8, "Bayview": 16, "Sunset District": 16, "Haight-Ashbury": 5, "Nob Hill": 11
    },
    "Golden Gate Park": {
        "Russian Hill": 19, "Marina District": 16, "Financial District": 26, "Alamo Square": 9,
        "The Castro": 13, "Bayview": 23, "Sunset District": 10, "Haight-Ashbury": 7, "Nob Hill": 20
    },
    "The Castro": {
        "Russian Hill": 18, "Marina District": 21, "Financial District": 21, "Alamo Square": 8,
        "Golden Gate Park": 11, "Bayview": 19, "Sunset District": 17, "Haight-Ashbury": 6, "Nob Hill": 16
    },
    "Bayview": {
        "Russian Hill": 23, "Marina District": 27, "Financial District": 19, "Alamo Square": 16,
        "Golden Gate Park": 22, "The Castro": 19, "Sunset District": 23, "Haight-Ashbury": 19, "Nob Hill": 20
    },
    "Sunset District": {
        "Russian Hill": 24, "Marina District": 21, "Financial District": 30, "Alamo Square": 17,
        "Golden Gate Park": 11, "The Castro": 17, "Bayview": 22, "Haight-Ashbury": 15, "Nob Hill": 27
    },
    "Haight-Ashbury": {
        "Russian Hill": 17, "Marina District": 17, "Financial District": 21, "Alamo Square": 5,
        "Golden Gate Park": 7, "The Castro": 6, "Bayview": 18, "Sunset District": 15, "Nob Hill": 15
    },
    "Nob Hill": {
        "Russian Hill": 5, "Marina District": 11, "Financial District": 9, "Alamo Square": 11,
        "Golden Gate Park": 17, "The Castro": 17, "Bayview": 19, "Sunset District": 24, "Haight-Ashbury": 13
    },
}

# Build optimizer
opt = Optimize()

names = list(people.keys())
N = len(names)

# Decision variables
meet = {p: Bool(f"meet_{p}") for p in names}
start = {p: Int(f"start_{p}") for p in names}
end = {p: Int(f"end_{p}") for p in names}
rank = {p: Int(f"rank_{p}") for p in names}

# Domains and basic constraints
for p in names:
    # Time bounds (0..24*60), though windows will further restrict
    opt.add(start[p] >= 0, start[p] <= hm(23, 59))
    opt.add(end[p] >= 0, end[p] <= hm(23, 59))
    # Rank domain
    opt.add(rank[p] >= 0, rank[p] <= N)

    # Availability and duration if meeting
    s_av = people[p]["start"]
    e_av = people[p]["end"]
    min_dur = people[p]["min"]

    opt.add(Implies(meet[p], And(start[p] >= s_av,
                                 end[p] <= e_av,
                                 end[p] - start[p] >= min_dur)))
    # If not met, collapse times to avoid weirdness (optional)
    opt.add(Implies(Not(meet[p]), And(rank[p] == 0)))
    # If met, must have positive rank
    opt.add(Implies(meet[p], rank[p] >= 1))

# At most one person per rank (1..N)
for r in range(1, N + 1):
    opt.add(AtMost(*[rank[p] == r for p in names], 1))

# Rank contiguity: if any assigned r+1, then some assigned r
for r in range(1, N):
    have_rp1 = Or(*[rank[p] == r + 1 for p in names])
    have_r = Or(*[rank[p] == r for p in names])
    opt.add(Implies(have_rp1, have_r))

# Total order non-overlap: if rank[p] < rank[q], then p ends before q starts
for i, p in enumerate(names):
    for j, q in enumerate(names):
        if i == j:
            continue
        opt.add(Implies(And(meet[p], meet[q], rank[p] < rank[q]), end[p] <= start[q]))

# Travel feasibility between consecutive ranks
for r in range(1, N):
    for p in names:
        for q in names:
            if p == q:
                continue
            loc_p = people[p]["loc"]
            loc_q = people[q]["loc"]
            tt = travel[loc_p][loc_q]
            opt.add(Implies(And(rank[p] == r, rank[q] == r + 1),
                            start[q] >= end[p] + tt))

# Anchor first meeting from start location/time
for p in names:
    tt0 = travel[start_location][people[p]["loc"]]
    opt.add(Implies(rank[p] == 1, start[p] >= start_time + tt0))

# Objective: maximize number of meetings
opt.maximize(Sum([If(meet[p], 1, 0) for p in names]))

# Solve
if opt.check() != sat:
    print(json.dumps({"itinerary": []}))
    exit(0)

m = opt.model()

# Extract chosen meetings
chosen = []
for p in names:
    if m.eval(meet[p]).is_true():
        s = m.eval(start[p]).as_long()
        e = m.eval(end[p]).as_long()
        chosen.append((m.eval(rank[p]).as_long(), p, s, e))

# Sort by rank
chosen.sort(key=lambda x: x[0])

itinerary = []
for _, person, s, e in chosen:
    itinerary.append({
        "action": "meet",
        "person": person,
        "start_time": min_to_str(s),
        "end_time": min_to_str(e)
    })

print(json.dumps({"itinerary": itinerary}))