# Requires: z3-solver (pip install z3-solver)
from z3 import *
import json
import re

# Time helpers
def t(h, m=0):
    return h * 60 + m

def mm_to_hhmm(x):
    h = x // 60
    m = x % 60
    return f"{h:02d}:{m:02d}"

# Neighborhoods
N = [
    "Presidio",
    "Pacific Heights",
    "Golden Gate Park",
    "Fisherman's Wharf",
    "Marina District",
    "Alamo Square",
    "Sunset District",
    "Nob Hill",
    "North Beach",
]

# Directed travel times (minutes). Include 0 for same-location travel.
travel = {a: {} for a in N}
def set_t(a, b, m):
    travel[a][b] = m

# Initialize all self-travel to 0
for a in N:
    for b in N:
        travel[a][b] = 0 if a == b else None

# Fill given travel times
set_t("Presidio", "Pacific Heights", 11)
set_t("Presidio", "Golden Gate Park", 12)
set_t("Presidio", "Fisherman's Wharf", 19)
set_t("Presidio", "Marina District", 11)
set_t("Presidio", "Alamo Square", 19)
set_t("Presidio", "Sunset District", 15)
set_t("Presidio", "Nob Hill", 18)
set_t("Presidio", "North Beach", 18)

set_t("Pacific Heights", "Presidio", 11)
set_t("Pacific Heights", "Golden Gate Park", 15)
set_t("Pacific Heights", "Fisherman's Wharf", 13)
set_t("Pacific Heights", "Marina District", 6)
set_t("Pacific Heights", "Alamo Square", 10)
set_t("Pacific Heights", "Sunset District", 21)
set_t("Pacific Heights", "Nob Hill", 8)
set_t("Pacific Heights", "North Beach", 9)

set_t("Golden Gate Park", "Presidio", 11)
set_t("Golden Gate Park", "Pacific Heights", 16)
set_t("Golden Gate Park", "Fisherman's Wharf", 24)
set_t("Golden Gate Park", "Marina District", 16)
set_t("Golden Gate Park", "Alamo Square", 9)
set_t("Golden Gate Park", "Sunset District", 10)
set_t("Golden Gate Park", "Nob Hill", 20)
set_t("Golden Gate Park", "North Beach", 23)

set_t("Fisherman's Wharf", "Presidio", 17)
set_t("Fisherman's Wharf", "Pacific Heights", 12)
set_t("Fisherman's Wharf", "Golden Gate Park", 25)
set_t("Fisherman's Wharf", "Marina District", 9)
set_t("Fisherman's Wharf", "Alamo Square", 21)
set_t("Fisherman's Wharf", "Sunset District", 27)
set_t("Fisherman's Wharf", "Nob Hill", 11)
set_t("Fisherman's Wharf", "North Beach", 6)

set_t("Marina District", "Presidio", 10)
set_t("Marina District", "Pacific Heights", 7)
set_t("Marina District", "Golden Gate Park", 18)
set_t("Marina District", "Fisherman's Wharf", 10)
set_t("Marina District", "Alamo Square", 15)
set_t("Marina District", "Sunset District", 19)
set_t("Marina District", "Nob Hill", 12)
set_t("Marina District", "North Beach", 11)

set_t("Alamo Square", "Presidio", 17)
set_t("Alamo Square", "Pacific Heights", 10)
set_t("Alamo Square", "Golden Gate Park", 9)
set_t("Alamo Square", "Fisherman's Wharf", 19)
set_t("Alamo Square", "Marina District", 15)
set_t("Alamo Square", "Sunset District", 16)
set_t("Alamo Square", "Nob Hill", 11)
set_t("Alamo Square", "North Beach", 15)

set_t("Sunset District", "Presidio", 16)
set_t("Sunset District", "Pacific Heights", 21)
set_t("Sunset District", "Golden Gate Park", 11)
set_t("Sunset District", "Fisherman's Wharf", 29)
set_t("Sunset District", "Marina District", 21)
set_t("Sunset District", "Alamo Square", 17)
set_t("Sunset District", "Nob Hill", 27)
set_t("Sunset District", "North Beach", 28)

set_t("Nob Hill", "Presidio", 17)
set_t("Nob Hill", "Pacific Heights", 8)
set_t("Nob Hill", "Golden Gate Park", 17)
set_t("Nob Hill", "Fisherman's Wharf", 10)
set_t("Nob Hill", "Marina District", 11)
set_t("Nob Hill", "Alamo Square", 11)
set_t("Nob Hill", "Sunset District", 24)
set_t("Nob Hill", "North Beach", 8)

set_t("North Beach", "Presidio", 17)
set_t("North Beach", "Pacific Heights", 8)
set_t("North Beach", "Golden Gate Park", 22)
set_t("North Beach", "Fisherman's Wharf", 5)
set_t("North Beach", "Marina District", 9)
set_t("North Beach", "Alamo Square", 16)
set_t("North Beach", "Sunset District", 27)
set_t("North Beach", "Nob Hill", 7)

# Replace None with a large number if any missing, but data appears complete for directed pairs
for a in N:
    for b in N:
        if travel[a][b] is None:
            # If any directed time not given, you could set a conservative high number or raise.
            # We'll set a large number to effectively block that route.
            travel[a][b] = 9999

# People with availability and minimum durations
people = [
    {"name": "Kevin",    "loc": "Pacific Heights",  "start": t(7,15),  "end": t(8,45),  "min": 90},
    {"name": "Michelle", "loc": "Golden Gate Park", "start": t(20,0),  "end": t(21,0), "min": 15},
    {"name": "Emily",    "loc": "Fisherman's Wharf","start": t(16,15), "end": t(19,0), "min": 30},
    {"name": "Mark",     "loc": "Marina District",  "start": t(18,15), "end": t(19,45),"min": 75},
    {"name": "Barbara",  "loc": "Alamo Square",     "start": t(17,0),  "end": t(19,0), "min": 120},
    {"name": "Laura",    "loc": "Sunset District",  "start": t(19,0),  "end": t(21,15),"min": 75},
    {"name": "Mary",     "loc": "Nob Hill",         "start": t(17,30), "end": t(19,0), "min": 45},
    {"name": "Helen",    "loc": "North Beach",      "start": t(11,0),  "end": t(12,15),"min": 45},
]

initial_loc = "Presidio"
arrival_time = t(9,0)

# Z3 model
opt = Optimize()

def sanitize(n):
    return re.sub(r'[^A-Za-z0-9_]', '_', n)

S = {}
E = {}
M = {}

for p in people:
    nm = sanitize(p["name"])
    S[nm] = Int(f"s_{nm}")
    E[nm] = Int(f"e_{nm}")
    M[nm] = Bool(f"meet_{nm}")
    # Time bounds
    opt.add(S[nm] >= 0, S[nm] <= 24*60)
    opt.add(E[nm] >= 0, E[nm] <= 24*60)
    # If meeting, enforce within window and duration
    opt.add(Implies(M[nm], And(S[nm] >= p["start"], E[nm] <= p["end"], E[nm] - S[nm] >= p["min"], S[nm] < E[nm])))
    # If not meeting, pin start=end (optional)
    opt.add(Implies(Not(M[nm]), S[nm] == E[nm]))
    # Initial reachability from Presidio at 09:00 (safe, even if not first)
    opt.add(Implies(M[nm], S[nm] >= arrival_time + travel[initial_loc][p["loc"]]))

# Pairwise non-overlap with travel
for i in range(len(people)):
    for j in range(i+1, len(people)):
        pi = people[i]
        pj = people[j]
        ni = sanitize(pi["name"])
        nj = sanitize(pj["name"])
        tij = travel[pi["loc"]][pj["loc"]]
        tji = travel[pj["loc"]][pi["loc"]]
        opt.add(Implies(And(M[ni], M[nj]), Or(E[ni] + tij <= S[nj], E[nj] + tji <= S[ni])))

# Objectives: maximize number of meetings, then total meeting minutes
num_meet = Sum([If(M[sanitize(p["name"])], 1, 0) for p in people])
tot_minutes = Sum([If(M[sanitize(p["name"])], E[sanitize(p["name"])] - S[sanitize(p["name"])], 0) for p in people])

opt.maximize(num_meet)
opt.maximize(tot_minutes)

if opt.check() != sat:
    print(json.dumps({"itinerary": []}))
else:
    model = opt.model()
    results = []
    for p in people:
        nm = sanitize(p["name"])
        if is_true(model[M[nm]]):
            s = model[S[nm]].as_long()
            e = model[E[nm]].as_long()
            results.append({
                "action": "meet",
                "person": p["name"],
                "start_time": mm_to_hhmm(s),
                "end_time": mm_to_hhmm(e),
            })
    # Sort by start time
    results.sort(key=lambda x: x["start_time"])
    print(json.dumps({"itinerary": results}))