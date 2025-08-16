# Requires: z3-solver (pip install z3-solver)
from z3 import *
import json

def minutes(h, m):
    return h * 60 + m

def fmt_time(t):
    return f"{t // 60:02d}:{t % 60:02d}"

# Locations
NB = "North Beach"
PH = "Pacific Heights"
CH = "Chinatown"
US = "Union Square"
MD = "Mission District"
GGP = "Golden Gate Park"
NH = "Nob Hill"

# Directed travel-time matrix (minutes)
T = {
    NB: {PH:8, CH:6, US:7, MD:18, GGP:22, NH:7},
    PH: {NB:9, CH:11, US:12, MD:15, GGP:15, NH:8},
    CH: {NB:3, PH:10, US:7, MD:18, GGP:23, NH:8},
    US: {NB:10, PH:15, CH:7, MD:14, GGP:22, NH:9},
    MD: {NB:17, PH:16, CH:16, US:15, GGP:17, NH:12},
    GGP:{NB:24, PH:16, CH:23, US:22, MD:17, NH:20},
    NH: {NB:8, PH:8, CH:6, US:7, MD:13, GGP:17},
}

# Ensure zero self-travel for convenience
for a in [NB, PH, CH, US, MD, GGP, NH]:
    T[a][a] = 0

# People data: name -> dict with location, availability [start, end], and min duration
people = {
    "James":   {"loc": PH,  "avail": (minutes(20,0), minutes(22,0)), "min": 120},
    "Robert":  {"loc": CH,  "avail": (minutes(12,15), minutes(16,45)), "min": 90},
    "Jeffrey": {"loc": US,  "avail": (minutes(9,30), minutes(15,30)), "min": 120},
    "Carol":   {"loc": MD,  "avail": (minutes(18,15), minutes(21,15)), "min": 15},
    "Mark":    {"loc": GGP, "avail": (minutes(11,30), minutes(17,45)), "min": 15},
    "Sandra":  {"loc": NH,  "avail": (minutes(8,0),  minutes(15,30)), "min": 15},
}

arrival_time = minutes(9,0)
arrival_loc = NB

# Z3 model
opt = Optimize()

start_vars = {}
end_vars = {}
meet_vars = {}

# Variable domains and basic constraints
for name, info in people.items():
    s = Int(f"start_{name}")
    e = Int(f"end_{name}")
    m = Bool(f"meet_{name}")
    start_vars[name] = s
    end_vars[name] = e
    meet_vars[name] = m

    min_dur = info["min"]
    a_start, a_end = info["avail"]
    loc = info["loc"]

    # Domains
    opt.add(And(s >= 0, s <= 24*60))
    opt.add(And(e >= 0, e <= 24*60))

    # If meeting, enforce availability window and duration
    opt.add(Implies(m, And(s >= a_start, e <= a_end, e == s + min_dur)))

    # If not meeting, set e = 0 (helps tie-breakers); s unconstrained beyond domain
    opt.add(Implies(Not(m), e == 0))

    # Cannot meet before arrival time; also must respect earliest reachable time from arrival
    opt.add(Implies(m, s >= arrival_time))
    opt.add(Implies(m, s >= arrival_time + T[arrival_loc][loc]))

# Travel-time no-overlap constraints for all pairs
names = list(people.keys())
for i in range(len(names)):
    for j in range(i+1, len(names)):
        ni, nj = names[i], names[j]
        li, lj = people[ni]["loc"], people[nj]["loc"]
        ei, ej = end_vars[ni], end_vars[nj]
        si, sj = start_vars[ni], start_vars[nj]
        mi, mj = meet_vars[ni], meet_vars[nj]

        # If both meetings happen, they must not overlap and include travel time
        opt.add(Implies(And(mi, mj),
                        Or(sj >= ei + T[li][lj],
                           si >= ej + T[lj][li])))

# Objective: maximize number of meetings
count_meet = Sum([If(meet_vars[n], 1, 0) for n in names])
opt.maximize(count_meet)

# Tie-breakers: minimize last end time (finish earlier if same count)
last_end = Int("last_end")
opt.add(last_end >= 0)
for n in names:
    opt.add(last_end >= end_vars[n])
opt.minimize(last_end)

# Solve
if opt.check() != sat:
    raise RuntimeError("No feasible schedule found")

model = opt.model()

# Build itinerary
meetings = []
for n in names:
    if is_true(model[meet_vars[n]]):
        s = model[start_vars[n]].as_long()
        e = model[end_vars[n]].as_long()
        meetings.append((s, n, s, e))

# Sort by start time
meetings.sort(key=lambda x: x[0])

itinerary = []
for _, n, s, e in meetings:
    itinerary.append({
        "action": "meet",
        "person": n,
        "start_time": fmt_time(s),
        "end_time": fmt_time(e)
    })

print(json.dumps({"itinerary": itinerary}))