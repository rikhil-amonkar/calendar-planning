# Requires: z3-solver (pip install z3-solver)
from z3 import Optimize, Int, Bool, If, And, Or, Implies, Sum
import json

def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

# Locations
FW = "Fisherman's Wharf"
BV = "Bayview"
GGP = "Golden Gate Park"
NH = "Nob Hill"
MD = "Marina District"
EMB = "Embarcadero"

# Directional travel times (minutes)
travel = {
    FW: {BV: 26, GGP: 25, NH: 11, MD: 9,  EMB: 8},
    BV: {FW: 25, GGP: 22, NH: 20, MD: 25, EMB: 19},
    GGP:{FW: 24, BV: 23, NH: 20, MD: 16, EMB: 25},
    NH: {FW: 11, BV: 19, GGP: 17, MD: 11, EMB: 9},
    MD: {FW: 10, BV: 27, GGP: 18, NH: 12, EMB: 14},
    EMB:{FW: 6,  BV: 21, GGP: 25, NH: 10, MD: 12},
}

# People: name, location, window (start, end), min duration
people = [
    {"name": "Thomas",    "loc": BV,  "start": to_minutes("15:30"), "end": to_minutes("18:30"), "min_dur": 120},
    {"name": "Stephanie", "loc": GGP, "start": to_minutes("18:30"), "end": to_minutes("21:45"), "min_dur": 30},
    {"name": "Laura",     "loc": NH,  "start": to_minutes("08:45"), "end": to_minutes("16:15"), "min_dur": 30},
    {"name": "Betty",     "loc": MD,  "start": to_minutes("18:45"), "end": to_minutes("21:45"), "min_dur": 45},
    {"name": "Patricia",  "loc": EMB, "start": to_minutes("17:30"), "end": to_minutes("22:00"), "min_dur": 45},
]

arrival_time = to_minutes("09:00")
start_loc = FW

opt = Optimize()

n = len(people)
meet = []
start_vars = []
end_vars = []

for i, p in enumerate(people):
    mi = Bool(f"meet_{i}")
    si = Int(f"start_{i}")
    ei = Int(f"end_{i}")
    meet.append(mi)
    start_vars.append(si)
    end_vars.append(ei)

    # Domains
    opt.add(si >= 0, ei >= 0)

    # If meeting, enforce availability window and min duration
    opt.add(Implies(mi, And(
        si >= p["start"],
        ei <= p["end"],
        ei - si >= p["min_dur"]
    )))
    # If not meeting, pin to 0 to avoid interfering with objectives
    opt.add(Implies(~mi, And(si == 0, ei == 0)))

    # Must be reachable from arrival at Fisherman's Wharf
    opt.add(Implies(mi, si >= arrival_time + travel[start_loc][p["loc"]]))

# Pairwise sequencing with travel time between meetings
for i in range(n):
    for j in range(i+1, n):
        li = people[i]["loc"]
        lj = people[j]["loc"]
        tij = travel[li][lj]
        tji = travel[lj][li]
        # If both meetings occur, either i before j with travel, or j before i with travel
        opt.add(Implies(And(meet[i], meet[j]),
                        Or(end_vars[i] + tij <= start_vars[j],
                           end_vars[j] + tji <= start_vars[i])))

# Objectives:
# 1) Maximize number of friends met
total_met = Sum([If(m, 1, 0) for m in meet])
opt.maximize(total_met)

# 2) Minimize the latest end time (finish the day as early as possible)
last_end = Int("last_end")
opt.add(last_end >= 0)
for i in range(n):
    opt.add(last_end >= end_vars[i])  # end_vars are 0 when not met
opt.minimize(last_end)

# 3) Minimize total meeting time (prefer minimum durations)
total_meeting_time = Sum([end_vars[i] - start_vars[i] for i in range(n)])
opt.minimize(total_meeting_time)

# 4) Minimize sum of start times (bias earlier starts)
opt.minimize(Sum(start_vars))

if opt.check() !=  sat:
    # If unsat, output empty itinerary
    print(json.dumps({"itinerary": []}))
else:
    m = opt.model()
    chosen = []
    for i, p in enumerate(people):
        if m.evaluate(meet[i]).is_true():
            s = m.evaluate(start_vars[i]).as_long()
            e = m.evaluate(end_vars[i]).as_long()
            chosen.append((s, {
                "action": "meet",
                "person": p["name"],
                "start_time": to_hhmm(s),
                "end_time": to_hhmm(e)
            }))
    chosen.sort(key=lambda x: x[0])
    itinerary = [entry for _, entry in chosen]
    print(json.dumps({"itinerary": itinerary}))