import json
from z3 import *

def minutes(h, m):
    return h * 60 + m

def minutes_to_str(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Locations
locations = [
    "Union Square",
    "Russian Hill",
    "Alamo Square",
    "Haight-Ashbury",
    "Marina District",
    "Bayview",
    "Chinatown",
    "Presidio",
    "Sunset District",
]

# Directed travel times in minutes (dictionary of dictionaries)
travel = {loc: {} for loc in locations}
def set_travel(frm, to, mins):
    travel[frm][to] = mins

# Fill travel times as provided
set_travel("Union Square", "Russian Hill", 13)
set_travel("Union Square", "Alamo Square", 15)
set_travel("Union Square", "Haight-Ashbury", 18)
set_travel("Union Square", "Marina District", 18)
set_travel("Union Square", "Bayview", 15)
set_travel("Union Square", "Chinatown", 7)
set_travel("Union Square", "Presidio", 24)
set_travel("Union Square", "Sunset District", 27)

set_travel("Russian Hill", "Union Square", 10)
set_travel("Russian Hill", "Alamo Square", 15)
set_travel("Russian Hill", "Haight-Ashbury", 17)
set_travel("Russian Hill", "Marina District", 7)
set_travel("Russian Hill", "Bayview", 23)
set_travel("Russian Hill", "Chinatown", 9)
set_travel("Russian Hill", "Presidio", 14)
set_travel("Russian Hill", "Sunset District", 23)

set_travel("Alamo Square", "Union Square", 14)
set_travel("Alamo Square", "Russian Hill", 13)
set_travel("Alamo Square", "Haight-Ashbury", 5)
set_travel("Alamo Square", "Marina District", 15)
set_travel("Alamo Square", "Bayview", 16)
set_travel("Alamo Square", "Chinatown", 15)
set_travel("Alamo Square", "Presidio", 17)
set_travel("Alamo Square", "Sunset District", 16)

set_travel("Haight-Ashbury", "Union Square", 19)
set_travel("Haight-Ashbury", "Russian Hill", 17)
set_travel("Haight-Ashbury", "Alamo Square", 5)
set_travel("Haight-Ashbury", "Marina District", 17)
set_travel("Haight-Ashbury", "Bayview", 18)
set_travel("Haight-Ashbury", "Chinatown", 19)
set_travel("Haight-Ashbury", "Presidio", 15)
set_travel("Haight-Ashbury", "Sunset District", 15)

set_travel("Marina District", "Union Square", 16)
set_travel("Marina District", "Russian Hill", 8)
set_travel("Marina District", "Alamo Square", 15)
set_travel("Marina District", "Haight-Ashbury", 16)
set_travel("Marina District", "Bayview", 27)
set_travel("Marina District", "Chinatown", 15)
set_travel("Marina District", "Presidio", 10)
set_travel("Marina District", "Sunset District", 19)

set_travel("Bayview", "Union Square", 18)
set_travel("Bayview", "Russian Hill", 23)
set_travel("Bayview", "Alamo Square", 16)
set_travel("Bayview", "Haight-Ashbury", 19)
set_travel("Bayview", "Marina District", 27)
set_travel("Bayview", "Chinatown", 19)
set_travel("Bayview", "Presidio", 32)
set_travel("Bayview", "Sunset District", 23)

set_travel("Chinatown", "Union Square", 7)
set_travel("Chinatown", "Russian Hill", 7)
set_travel("Chinatown", "Alamo Square", 17)
set_travel("Chinatown", "Haight-Ashbury", 19)
set_travel("Chinatown", "Marina District", 12)
set_travel("Chinatown", "Bayview", 20)
set_travel("Chinatown", "Presidio", 19)
set_travel("Chinatown", "Sunset District", 29)

set_travel("Presidio", "Union Square", 22)
set_travel("Presidio", "Russian Hill", 14)
set_travel("Presidio", "Alamo Square", 19)
set_travel("Presidio", "Haight-Ashbury", 15)
set_travel("Presidio", "Marina District", 11)
set_travel("Presidio", "Bayview", 31)
set_travel("Presidio", "Chinatown", 21)
set_travel("Presidio", "Sunset District", 15)

set_travel("Sunset District", "Union Square", 30)
set_travel("Sunset District", "Russian Hill", 24)
set_travel("Sunset District", "Alamo Square", 17)
set_travel("Sunset District", "Haight-Ashbury", 15)
set_travel("Sunset District", "Marina District", 21)
set_travel("Sunset District", "Bayview", 22)
set_travel("Sunset District", "Chinatown", 30)
set_travel("Sunset District", "Presidio", 16)

# Ensure zero self travel times
for a in locations:
    travel[a][a] = 0

# People data: index 1..N
people = [
    # name, location, avail_start_min, avail_end_min, min_duration
    ("Betty",   "Russian Hill",   minutes(7,0),   minutes(16,45), 105),
    ("Melissa", "Alamo Square",   minutes(9,30),  minutes(17,15), 105),
    ("Joshua",  "Haight-Ashbury", minutes(12,15), minutes(19,0),   90),
    ("Jeffrey", "Marina District",minutes(12,15), minutes(18,0),   45),
    ("James",   "Bayview",        minutes(7,30),  minutes(20,0),   90),
    ("Anthony", "Chinatown",      minutes(11,45), minutes(13,30),  75),
    ("Timothy", "Presidio",       minutes(12,30), minutes(14,45),  90),
    ("Emily",   "Sunset District",minutes(19,30), minutes(21,30), 120),
]
N = len(people)

# Map indices to names/locations (0 is START at Union Square)
index_to_name = ["START"] + [p[0] for p in people]
index_to_loc  = ["Union Square"] + [p[1] for p in people]
avail_start   = [minutes(9,0)] + [p[2] for p in people]  # START window is exactly 9:00-9:00
avail_end     = [minutes(9,0)] + [p[3] for p in people]
min_dur       = [0] + [p[4] for p in people]

# Helper to build piecewise selection from index
def select_expr(idx_var, arr):
    # arr is a list indexed 0..N of z3 Int expressions
    expr = arr[0]
    for i in range(1, N+1):
        expr = If(idx_var == i, arr[i], expr)
    return expr

# Helper to build travel time expression based on two index vars
def travel_expr(i_idx, j_idx):
    # Build inner selection for destination
    def select_travel_from(i_const, j_idx):
        base = IntVal(travel[index_to_loc[i_const]][index_to_loc[0]])
        for j in range(1, N+1):
            base = If(j_idx == j, IntVal(travel[index_to_loc[i_const]][index_to_loc[j]]), base)
        return base
    expr = select_travel_from(0, j_idx)
    for i in range(1, N+1):
        expr = If(i_idx == i, select_travel_from(i, j_idx), expr)
    return expr

# Z3 model
opt = Optimize()

# Variables for each person (index 1..N)
meet = [Bool(f"meet_{i}") for i in range(N+1)]  # include index 0 for START
start_vars = [Int(f"start_{i}") for i in range(N+1)]
end_vars = [Int(f"end_{i}") for i in range(N+1)]

# START constraints (index 0)
opt.add(meet[0] == True)
opt.add(start_vars[0] == minutes(9,0))
opt.add(end_vars[0] == minutes(9,0))

# Person constraints
for i in range(1, N+1):
    s = start_vars[i]
    e = end_vars[i]
    opt.add(Implies(meet[i],
                    And(s >= avail_start[i],
                        e <= avail_end[i],
                        e - s >= min_dur[i])))
    opt.add(Implies(Not(meet[i]), And(s == 0, e == 0)))
    opt.add(s >= 0, e >= 0, e >= s)

# Ordering: positions 1..N (0 unused)
P = N
order = [Int(f"order_{k}") for k in range(1, P+1)]
used = [Bool(f"used_{k}") for k in range(1, P+1)]

# Domain and used equivalence
for k in range(P):
    # Domain: 0..N
    opt.add(And(order[k] >= 0, order[k] <= N))
    opt.add(used[k] == (order[k] != 0))

# Contiguity: used_k implies used_{k-1}
for k in range(1, P):
    opt.add(Implies(used[k], used[k-1]))

# Each person is met iff appears in order
for i in range(1, N+1):
    opt.add(meet[i] == Or([order[k] == i for k in range(P)]))

# AllDifferent among used positions (ignore zeros)
for a in range(P):
    for b in range(a+1, P):
        opt.add(Implies(And(used[a], used[b]), order[a] != order[b]))

# Sequencing constraints:
# From START to first used
if P >= 1:
    first_idx = order[0]
    first_start = select_expr(first_idx, start_vars)
    # travel from index 0 (START/Union Square) to first meeting
    opt.add(Implies(used[0], first_start >= end_vars[0] + travel_expr(IntVal(0), first_idx)))

# Between consecutive used positions
for k in range(P-1):
    cur_idx = order[k]
    nxt_idx = order[k+1]
    cur_end = select_expr(cur_idx, end_vars)
    nxt_start = select_expr(nxt_idx, start_vars)
    opt.add(Implies(And(used[k], used[k+1]),
                    nxt_start >= cur_end + travel_expr(cur_idx, nxt_idx)))

# Objective: maximize number of meetings (exclude START), then maximize total meeting time
total_meetings = Sum([If(meet[i], 1, 0) for i in range(1, N+1)])
total_meeting_minutes = Sum([If(meet[i], end_vars[i] - start_vars[i], 0) for i in range(1, N+1)])
opt.maximize(total_meetings)
opt.maximize(total_meeting_minutes)

# Solve
if opt.check() != sat:
    print(json.dumps({"itinerary": []}))
    exit()

model = opt.model()

# Build itinerary in order
itinerary = []
for k in range(P):
    if model.eval(used[k], model_completion=True):
        idx = model.eval(order[k]).as_long()
        if idx == 0:
            continue
        person = index_to_name[idx]
        loc = index_to_loc[idx]
        s = model.eval(start_vars[idx]).as_long()
        e = model.eval(end_vars[idx]).as_long()
        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": person,
            "start_time": minutes_to_str(s),
            "end_time": minutes_to_str(e)
        })
    else:
        break

print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))