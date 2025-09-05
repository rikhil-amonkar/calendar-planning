import json
from z3 import Optimize, Int, Bool, Sum, If, And, Or, Implies, is_true

# Helper functions
def t_to_min(s):
    h, m = s.split(":")
    return int(h) * 60 + int(m)

def min_to_t(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Locations
FD = "Financial District"
FW = "Fisherman's Wharf"
PH = "Pacific Heights"
MD = "Mission District"

# Travel times in minutes (asymmetric where specified)
travel = {
    FD: {FW: 10, PH: 13, MD: 17},
    FW: {FD: 11, PH: 12, MD: 22},
    PH: {FD: 13, FW: 13, MD: 15},
    MD: {FD: 17, FW: 22, PH: 16},
}

# People data: location, availability window, minimum meeting duration
people = {
    "David":   {"location": FW, "avail_start": t_to_min("10:45"), "avail_end": t_to_min("15:30"), "min_dur": 15},
    "Timothy": {"location": PH, "avail_start": t_to_min("9:00"),  "avail_end": t_to_min("15:30"), "min_dur": 75},
    "Robert":  {"location": MD, "avail_start": t_to_min("12:15"), "avail_end": t_to_min("19:45"), "min_dur": 90},
}

day_start_loc = FD
day_start_time = t_to_min("9:00")

# Z3 variables
opt = Optimize()
opt.set('priority', 'lex')  # Maximize attendees, then total duration, then minimize finish time

starts = {}
ends = {}
durs = {}
use = {}
for person in people:
    starts[person] = Int(f"start_{person}")
    ends[person]   = Int(f"end_{person}")
    durs[person]   = Int(f"dur_{person}")
    use[person]    = Bool(f"use_{person}")

# Base constraints
for person, info in people.items():
    loc = info["location"]
    avail_s = info["avail_start"]
    avail_e = info["avail_end"]
    min_d = info["min_dur"]

    s = starts[person]
    e = ends[person]
    d = durs[person]
    u = use[person]

    # Non-negativity and linking end = start + duration
    opt.add(s >= 0, d >= 0, e >= 0)
    opt.add(e == s + d)

    # If meeting is scheduled
    opt.add(Implies(u, And(
        s >= avail_s,
        e <= avail_e,
        d >= min_d,
        # Must be reachable from starting point at day start
        s >= day_start_time + travel[day_start_loc][loc]
    )))

    # If not scheduled, zero everything to avoid spurious contributions
    opt.add(Implies(And(Not(u)), And(
        d == 0,
        s == 0,
        e == 0
    )))

# Pairwise non-overlap with travel times if both meetings occur
persons = list(people.keys())
for i in range(len(persons)):
    for j in range(i + 1, len(persons)):
        p = persons[i]
        q = persons[j]
        loc_p = people[p]["location"]
        loc_q = people[q]["location"]
        s_p, e_p = starts[p], ends[p]
        s_q, e_q = starts[q], ends[q]
        u_p, u_q = use[p], use[q]

        # If both meetings are chosen, enforce sequencing with travel time
        opt.add(Implies(And(u_p, u_q),
                        Or(
                            e_p + travel[loc_p][loc_q] <= s_q,
                            e_q + travel[loc_q][loc_p] <= s_p
                        )))

# Objective 1: maximize number of friends met
attendees = Sum([If(use[p], 1, 0) for p in persons])
opt.maximize(attendees)

# Objective 2: maximize total meeting duration
total_duration = Sum([If(use[p], durs[p], 0) for p in persons])
opt.maximize(total_duration)

# Objective 3: minimize finish time (the last meeting end)
finish_time = Int("finish_time")
opt.add(finish_time >= day_start_time)
for p in persons:
    opt.add(finish_time >= ends[p])
opt.minimize(finish_time)

# Solve
if opt.check().r == 1:  # sat
    model = opt.model()
    itinerary = []
    for p in persons:
        if is_true(model.eval(use[p], model_completion=True)):
            start_min = model.eval(starts[p], model_completion=True).as_long()
            end_min = model.eval(ends[p], model_completion=True).as_long()
            itinerary.append({
                "action": "meet",
                "location": people[p]["location"],
                "person": p,
                "start_time": min_to_t(start_min),
                "end_time": min_to_t(end_min),
            })
    # Sort by start time
    itinerary.sort(key=lambda x: t_to_min(x["start_time"]))
    result = {"itinerary": itinerary}
else:
    result = {"itinerary": []}

print(json.dumps(result))