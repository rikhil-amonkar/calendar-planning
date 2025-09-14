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
    "Alamo Square",
    "Russian Hill",
    "Presidio",
    "Chinatown",
    "Sunset District",
    "The Castro",
    "Embarcadero",
    "Golden Gate Park"
]

# Travel times (in minutes) as a dictionary of (from, to) -> minutes
distances = {
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Presidio"): 18,
    ("Alamo Square", "Chinatown"): 16,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Embarcadero"): 17,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Presidio", "Alamo Square"): 18,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Golden Gate Park"): 12,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Embarcadero"): 31,
    ("Sunset District", "Golden Gate Park"): 11,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Chinatown"): 20,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Golden Gate Park"): 11,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Golden Gate Park", "Alamo Square"): 10,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Embarcadero"): 25,
}

def dist(a, b):
    return distances[(a, b)]

# Start parameters
start_location = "Alamo Square"
start_time = minutes(9, 0)  # 9:00

# Friends constraints
friends = [
    {"name": "Emily",   "location": "Russian Hill",    "avail_start": minutes(12,15), "avail_end": minutes(14,15), "min_duration": 105},
    {"name": "Mark",    "location": "Presidio",        "avail_start": minutes(14,45), "avail_end": minutes(19,30), "min_duration": 60},
    {"name": "Deborah", "location": "Chinatown",       "avail_start": minutes(7,30),  "avail_end": minutes(15,30), "min_duration": 45},
    {"name": "Margaret","location": "Sunset District", "avail_start": minutes(21,30), "avail_end": minutes(22,30), "min_duration": 60},
    {"name": "George",  "location": "The Castro",      "avail_start": minutes(7,30),  "avail_end": minutes(14,15), "min_duration": 60},
    {"name": "Andrew",  "location": "Embarcadero",     "avail_start": minutes(20,15), "avail_end": minutes(22,0),  "min_duration": 75},
    {"name": "Steven",  "location": "Golden Gate Park","avail_start": minutes(11,15), "avail_end": minutes(21,15), "min_duration": 105},
]

# Z3 model
opt = Optimize()

# Variables
N = len(friends)
s_vars = {}
e_vars = {}
d_vars = {}
pos_vars = {}
meet_vars = {}

def var_name(prefix, name):
    return f"{prefix}_{name.replace(' ', '_')}"

for f in friends:
    n = f["name"]
    s = Int(var_name("s", n))
    e = Int(var_name("e", n))
    d = Int(var_name("dur", n))
    p = Int(var_name("pos", n))
    m = Bool(var_name("meet", n))
    s_vars[n] = s
    e_vars[n] = e
    d_vars[n] = d
    pos_vars[n] = p
    meet_vars[n] = m

    # Bounds
    opt.add(s >= 0, s <= 24*60)
    opt.add(e >= 0, e <= 24*60)
    opt.add(d >= 0, d <= 24*60)
    opt.add(p >= 0, p <= N)

    # Meet implies schedule within availability and duration
    opt.add(Implies(m, And(
        s >= f["avail_start"],
        e <= f["avail_end"],
        d >= f["min_duration"],
        e == s + d
    )))
    # Not meet implies zeroed times and position 0
    opt.add(Implies(Not(m), And(s == 0, e == 0, d == 0, p == 0)))

    # Meet <-> pos >= 1
    opt.add(Implies(m, p >= 1))
    opt.add(Implies(p == 0, Not(m)))

# Distinct positions among meetings
for i in range(N):
    for j in range(i+1, N):
        ni = friends[i]["name"]
        nj = friends[j]["name"]
        mi = meet_vars[ni]
        mj = meet_vars[nj]
        pi = pos_vars[ni]
        pj = pos_vars[nj]
        # If both are met, their positions must be distinct
        opt.add(Implies(And(mi, mj), pi != pj))

# Travel/order constraints
for i in range(N):
    for j in range(N):
        if i == j:
            continue
        fi = friends[i]
        fj = friends[j]
        ni = fi["name"]
        nj = fj["name"]
        mi = meet_vars[ni]
        mj = meet_vars[nj]
        pi = pos_vars[ni]
        pj = pos_vars[nj]
        si = s_vars[ni]
        ei = e_vars[ni]
        sj = s_vars[nj]
        # If i is scheduled before j, enforce travel time between them
        opt.add(Implies(And(mi, mj, pi < pj), sj >= ei + dist(fi["location"], fj["location"])))

# Ensure there is a first meeting (pos == 1) iff there is any meeting
first_candidates = [And(meet_vars[f["name"]], pos_vars[f["name"]] == 1) for f in friends]
any_meeting = Or([meet_vars[f["name"]] for f in friends]) if friends else False
opt.add(Or(first_candidates) == any_meeting)

# Start constraint: if a meeting is first, account for travel from start location/time
for f in friends:
    n = f["name"]
    s = s_vars[n]
    m = meet_vars[n]
    p = pos_vars[n]
    opt.add(Implies(And(m, p == 1), s >= start_time + dist(start_location, f["location"])))

# Objectives: maximize number of friends met, then maximize total meeting time
meet_count = Sum([If(meet_vars[f["name"]], 1, 0) for f in friends])
total_duration = Sum([d_vars[f["name"]] for f in friends])
opt.maximize(meet_count)
opt.maximize(total_duration)

# Solve
if opt.check() != sat:
    # No feasible plan
    output = {"itinerary": []}
    print(json.dumps(output))
else:
    model = opt.model()
    # Collect scheduled meetings
    scheduled = []
    for f in friends:
        n = f["name"]
        if is_true(model.evaluate(meet_vars[n])):
            pos = model.evaluate(pos_vars[n]).as_long()
            s = model.evaluate(s_vars[n]).as_long()
            e = model.evaluate(e_vars[n]).as_long()
            scheduled.append({
                "pos": pos,
                "action": "meet",
                "location": f["location"],
                "person": n,
                "start_time": fmt_time(s),
                "end_time": fmt_time(e)
            })

    # Sort by position
    scheduled.sort(key=lambda x: x["pos"])
    # Remove helper 'pos'
    itinerary = [{"action": m["action"], "location": m["location"], "person": m["person"], "start_time": m["start_time"], "end_time": m["end_time"]} for m in scheduled]

    print(json.dumps({"itinerary": itinerary}))