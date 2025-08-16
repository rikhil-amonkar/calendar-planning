# Requires: z3-solver (pip install z3-solver)
from z3 import *
import json

# Time helper: convert minutes since 09:00 to HH:MM 24-hour
def fmt(mins_from_9):
    abs_min = 9*60 + mins_from_9
    h = abs_min // 60
    m = abs_min % 60
    return f"{h:02d}:{m:02d}"

# Travel times (minutes), directional as provided
travel = {
    "Union Square": {
        "Mission District": 14, "Fisherman's Wharf": 15, "Russian Hill": 13, "Marina District": 18,
        "North Beach": 10, "Chinatown": 7, "Pacific Heights": 15, "The Castro": 17, "Nob Hill": 9, "Sunset District": 27
    },
    "Mission District": {
        "Union Square": 15, "Fisherman's Wharf": 22, "Russian Hill": 15, "Marina District": 19,
        "North Beach": 17, "Chinatown": 16, "Pacific Heights": 16, "The Castro": 7, "Nob Hill": 12, "Sunset District": 24
    },
    "Fisherman's Wharf": {
        "Union Square": 13, "Mission District": 22, "Russian Hill": 7, "Marina District": 9,
        "North Beach": 6, "Chinatown": 12, "Pacific Heights": 12, "The Castro": 27, "Nob Hill": 11, "Sunset District": 27
    },
    "Russian Hill": {
        "Union Square": 10, "Mission District": 16, "Fisherman's Wharf": 7, "Marina District": 7,
        "North Beach": 5, "Chinatown": 9, "Pacific Heights": 7, "The Castro": 21, "Nob Hill": 5, "Sunset District": 23
    },
    "Marina District": {
        "Union Square": 16, "Mission District": 20, "Fisherman's Wharf": 10, "Russian Hill": 8,
        "North Beach": 11, "Chinatown": 15, "Pacific Heights": 7, "The Castro": 22, "Nob Hill": 12, "Sunset District": 19
    },
    "North Beach": {
        "Union Square": 7, "Mission District": 18, "Fisherman's Wharf": 5, "Russian Hill": 4,
        "Marina District": 9, "Chinatown": 6, "Pacific Heights": 8, "The Castro": 23, "Nob Hill": 7, "Sunset District": 27
    },
    "Chinatown": {
        "Union Square": 7, "Mission District": 17, "Fisherman's Wharf": 8, "Russian Hill": 7,
        "Marina District": 12, "North Beach": 3, "Pacific Heights": 10, "The Castro": 22, "Nob Hill": 9, "Sunset District": 29
    },
    "Pacific Heights": {
        "Union Square": 12, "Mission District": 15, "Fisherman's Wharf": 13, "Russian Hill": 7,
        "Marina District": 6, "North Beach": 9, "Chinatown": 11, "The Castro": 16, "Nob Hill": 8, "Sunset District": 21
    },
    "The Castro": {
        "Union Square": 19, "Mission District": 7, "Fisherman's Wharf": 24, "Russian Hill": 18,
        "Marina District": 21, "North Beach": 20, "Chinatown": 22, "Pacific Heights": 16, "Nob Hill": 16, "Sunset District": 17
    },
    "Nob Hill": {
        "Union Square": 7, "Mission District": 13, "Fisherman's Wharf": 10, "Russian Hill": 5,
        "Marina District": 11, "North Beach": 8, "Chinatown": 6, "Pacific Heights": 8, "The Castro": 17, "Sunset District": 24
    },
    "Sunset District": {
        "Union Square": 30, "Mission District": 25, "Fisherman's Wharf": 29, "Russian Hill": 24,
        "Marina District": 21, "North Beach": 28, "Chinatown": 30, "Pacific Heights": 21, "The Castro": 17, "Nob Hill": 27
    }
}

# People with location, availability window (minutes since 09:00), and minimum meeting duration
people = {
    "Kevin":   {"loc": "Mission District",     "window": (705, 765), "min_dur": 60},
    "Mark":    {"loc": "Fisherman's Wharf",    "window": (495, 660), "min_dur": 90},
    "Jessica": {"loc": "Russian Hill",         "window": (0, 360),   "min_dur": 120},
    "Jason":   {"loc": "Marina District",      "window": (375, 765), "min_dur": 120},
    "John":    {"loc": "North Beach",          "window": (45, 540),  "min_dur": 15},
    "Karen":   {"loc": "Chinatown",            "window": (465, 600), "min_dur": 75},
    "Sarah":   {"loc": "Pacific Heights",      "window": (510, 555), "min_dur": 45},
    "Amanda":  {"loc": "The Castro",           "window": (660, 735), "min_dur": 60},
    "Nancy":   {"loc": "Nob Hill",             "window": (45, 240),  "min_dur": 45},
    "Rebecca": {"loc": "Sunset District",      "window": (-15, 360), "min_dur": 75},
}

start_loc = "Union Square"
horizon = 780  # until 22:00

# Z3 model
opt = Optimize()

# Variables per person
vars_start = {}
vars_end = {}
vars_meet = {}

for p, info in people.items():
    s = Int(f"start_{p}")
    e = Int(f"end_{p}")
    m = Bool(f"meet_{p}")
    vars_start[p] = s
    vars_end[p] = e
    vars_meet[p] = m

    ws, we = info["window"]
    ws_eff = max(0, ws)
    we_eff = min(horizon, we)
    min_d = info["min_dur"]
    # Basic bounds
    opt.add(s >= 0, e >= 0, s <= horizon, e <= horizon)
    # Meeting window and duration if selected
    opt.add(Implies(m, And(s >= ws_eff, e <= we_eff, e - s >= min_d)))
    # If not meeting, force zero-length to simplify (optional)
    opt.add(Implies(Not(m), And(s == 0, e == 0)))
    # Reachability from start location
    # Only add if travel time known; it is for all
    t0 = travel[start_loc][info["loc"]]
    opt.add(Implies(m, s >= t0))

# Pairwise non-overlap with travel times using an ordering boolean
people_list = list(people.keys())
order_bools = {}
for i in range(len(people_list)):
    for j in range(i+1, len(people_list)):
        pi = people_list[i]
        pj = people_list[j]
        bi = Bool(f"{pi}_before_{pj}")
        order_bools[(pi, pj)] = bi
        li = people[pi]["loc"]
        lj = people[pj]["loc"]
        tij = travel[li][lj]
        tji = travel[lj][li]
        si, ei, mi = vars_start[pi], vars_end[pi], vars_meet[pi]
        sj, ej, mj = vars_start[pj], vars_end[pj], vars_meet[pj]
        # If both are met, one must be scheduled before the other with travel time buffers
        opt.add(Implies(And(mi, mj, bi), ei + tij <= sj))
        opt.add(Implies(And(mi, mj, Not(bi)), ej + tji <= si))
        # If either not met, no constraint needed (guards above handle it)

# Objective: maximize number of meetings
total_meets = Sum([If(vars_meet[p], 1, 0) for p in people_list])
opt.maximize(total_meets)

# Secondary objective: minimize the day end time (helps pick earlier-feasible max solutions)
day_end = Int("day_end")
opt.add(day_end >= 0)
for p in people_list:
    opt.add(day_end >= vars_end[p])
opt.minimize(day_end)

# Solve
if opt.check() != sat:
    raise RuntimeError("No feasible schedule found")

model = opt.model()

# Extract solution
meetings = []
for p in people_list:
    if is_true(model[vars_meet[p]]):
        s = model[vars_start[p]].as_long()
        e = model[vars_end[p]].as_long()
        meetings.append((s, e, p))

# Sort by start time
meetings.sort(key=lambda x: x[0])

# Build itinerary JSON
itinerary = []
for s, e, p in meetings:
    itinerary.append({
        "action": "meet",
        "person": p,
        "start_time": fmt(s),
        "end_time": fmt(e)
    })

print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))