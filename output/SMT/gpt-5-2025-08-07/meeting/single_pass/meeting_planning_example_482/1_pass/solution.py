# Requires: z3-solver (pip install z3-solver)
from z3 import *
import json

def hm_to_min(s):
    h, m = map(int, s.split(":"))
    return h * 60 + m

def min_to_hm(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

# Data
start_loc = "Haight-Ashbury"
start_time = hm_to_min("09:00")

people = [
    "Stephanie",
    "Sandra",
    "Richard",
    "Brian",
    "Jason",
]

location = {
    "Stephanie": "Mission District",
    "Sandra": "Bayview",
    "Richard": "Pacific Heights",
    "Brian": "Russian Hill",
    "Jason": "Fisherman's Wharf",
}

# Availability windows
avail = {
    "Stephanie": (hm_to_min("08:15"), hm_to_min("13:45")),
    "Sandra": (hm_to_min("13:00"), hm_to_min("19:30")),
    "Richard": (hm_to_min("07:15"), hm_to_min("10:15")),
    "Brian": (hm_to_min("12:15"), hm_to_min("16:00")),
    "Jason": (hm_to_min("08:30"), hm_to_min("17:45")),
}

# Minimum meeting durations (minutes)
min_dur = {
    "Stephanie": 90,
    "Sandra": 15,
    "Richard": 75,
    "Brian": 120,
    "Jason": 60,
}

# Directed travel times (minutes)
travel = {
    "Haight-Ashbury": {
        "Mission District": 11,
        "Bayview": 18,
        "Pacific Heights": 12,
        "Russian Hill": 17,
        "Fisherman's Wharf": 23,
    },
    "Mission District": {
        "Haight-Ashbury": 12,
        "Bayview": 15,
        "Pacific Heights": 16,
        "Russian Hill": 15,
        "Fisherman's Wharf": 22,
    },
    "Bayview": {
        "Haight-Ashbury": 19,
        "Mission District": 13,
        "Pacific Heights": 23,
        "Russian Hill": 23,
        "Fisherman's Wharf": 25,
    },
    "Pacific Heights": {
        "Haight-Ashbury": 11,
        "Mission District": 15,
        "Bayview": 22,
        "Russian Hill": 7,
        "Fisherman's Wharf": 13,
    },
    "Russian Hill": {
        "Haight-Ashbury": 17,
        "Mission District": 16,
        "Bayview": 23,
        "Pacific Heights": 7,
        "Fisherman's Wharf": 7,
    },
    "Fisherman's Wharf": {
        "Haight-Ashbury": 22,
        "Mission District": 22,
        "Bayview": 26,
        "Pacific Heights": 12,
        "Russian Hill": 7,
    },
}

# Model
opt = Optimize()

meet = {p: Bool(f"meet_{p}") for p in people}
s = {p: Int(f"start_{p}") for p in people}
e = {p: Int(f"end_{p}") for p in people}

# Time domain bounds
for p in people:
    opt.add(s[p] >= 0, s[p] <= 24 * 60)
    opt.add(e[p] >= 0, e[p] <= 24 * 60)

# Availability, durations, and inactive meeting times fixed to 0
for p in people:
    a_start, a_end = avail[p]
    dur = min_dur[p]
    opt.add(Implies(meet[p], And(
        s[p] >= a_start,
        e[p] <= a_end,
        e[p] - s[p] >= dur
    )))
    opt.add(Implies(Not(meet[p]), And(s[p] == 0, e[p] == 0)))

# Non-overlap with travel between every pair of meetings
for i in range(len(people)):
    for j in range(i + 1, len(people)):
        pi, pj = people[i], people[j]
        li, lj = location[pi], location[pj]
        tij = travel[li][lj]
        tji = travel[lj][li]
        opt.add(Implies(And(meet[pi], meet[pj]),
                        Or(s[pj] >= e[pi] + tij,
                           s[pi] >= e[pj] + tji)))

# Anchor: first meeting must be reachable from start; others can be after a previous meeting
for i, pi in enumerate(people):
    li = location[pi]
    disj = [s[pi] >= start_time + travel[start_loc][li]]
    for j, pj in enumerate(people):
        if i == j:
            continue
        lj = location[pj]
        disj.append(And(meet[pj], s[pi] >= e[pj] + travel[lj][li]))
    opt.add(Implies(meet[pi], Or(disj)))

# Objectives:
# 1) Maximize number of friends met
opt.maximize(Sum([If(meet[p], 1, 0) for p in people]))
# 2) Minimize total meeting time (prefer minimum durations to allow more feasible chains)
opt.minimize(Sum([If(meet[p], e[p] - s[p], 0) for p in people]))
# 3) Minimize the latest end time among meetings (earlier finish)
L = Int("latest_end")
opt.add(L >= start_time)
for p in people:
    opt.add(Implies(meet[p], e[p] <= L))
opt.minimize(L)

# Solve
if opt.check() != sat:
    print(json.dumps({"itinerary": []}))
else:
    m = opt.model()
    selected = []
    for p in people:
        if m.evaluate(meet[p], model_completion=True):
            start_min = m.evaluate(s[p], model_completion=True).as_long()
            end_min = m.evaluate(e[p], model_completion=True).as_long()
            selected.append({
                "action": "meet",
                "person": p,
                "start_time": min_to_hm(start_min),
                "end_time": min_to_hm(end_min),
                "location": location[p]
            })

    # Sort by start time
    selected.sort(key=lambda x: x["start_time"])

    # Output only required fields
    itinerary = [{"action": "meet", "person": x["person"], "start_time": x["start_time"], "end_time": x["end_time"]} for x in selected]
    print(json.dumps({"itinerary": itinerary}))