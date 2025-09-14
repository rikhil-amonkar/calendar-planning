import json
from z3 import *

def time_to_min(t):
    h, m = t.split(':')
    return int(h) * 60 + int(m)

def min_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Locations
locations = [
    "Nob Hill",
    "Richmond District",
    "Financial District",
    "North Beach",
    "The Castro",
    "Golden Gate Park",
]

# Travel times in minutes (directed)
travel = {
    "Nob Hill": {
        "Richmond District": 14,
        "Financial District": 9,
        "North Beach": 8,
        "The Castro": 17,
        "Golden Gate Park": 17,
    },
    "Richmond District": {
        "Nob Hill": 17,
        "Financial District": 22,
        "North Beach": 17,
        "The Castro": 16,
        "Golden Gate Park": 9,
    },
    "Financial District": {
        "Nob Hill": 8,
        "Richmond District": 21,
        "North Beach": 7,
        "The Castro": 23,
        "Golden Gate Park": 23,
    },
    "North Beach": {
        "Nob Hill": 7,
        "Richmond District": 18,
        "Financial District": 8,
        "The Castro": 22,
        "Golden Gate Park": 22,
    },
    "The Castro": {
        "Nob Hill": 16,
        "Richmond District": 16,
        "Financial District": 20,
        "North Beach": 20,
        "Golden Gate Park": 11,
    },
    "Golden Gate Park": {
        "Nob Hill": 20,
        "Richmond District": 7,
        "Financial District": 26,
        "North Beach": 24,
        "The Castro": 13,
    },
}

def t(from_loc, to_loc):
    return travel[from_loc][to_loc]

# Start info
start_location = "Nob Hill"
start_time = time_to_min("9:00")

# People data
people = {
    "Emily": {
        "location": "Richmond District",
        "avail_start": time_to_min("19:00"),
        "avail_end": time_to_min("21:00"),
        "min_dur": 15,
    },
    "Margaret": {
        "location": "Financial District",
        "avail_start": time_to_min("16:30"),
        "avail_end": time_to_min("20:15"),
        "min_dur": 75,
    },
    "Ronald": {
        "location": "North Beach",
        "avail_start": time_to_min("18:30"),
        "avail_end": time_to_min("19:30"),
        "min_dur": 45,
    },
    "Deborah": {
        "location": "The Castro",
        "avail_start": time_to_min("13:45"),
        "avail_end": time_to_min("21:15"),
        "min_dur": 90,
    },
    "Jeffrey": {
        "location": "Golden Gate Park",
        "avail_start": time_to_min("11:15"),
        "avail_end": time_to_min("14:30"),
        "min_dur": 120,
    },
}

# Z3 model
opt = Optimize()

meet = {}
start_vars = {}
end_vars = {}

for person in people:
    meet[person] = Bool(f"meet_{person}")
    start_vars[person] = Int(f"start_{person}")
    end_vars[person] = Int(f"end_{person}")

    # General bounds
    opt.add(start_vars[person] >= 0, end_vars[person] >= 0, end_vars[person] >= start_vars[person])

    # If meeting, enforce availability and minimum durations
    ps = people[person]
    loc = ps["location"]

    opt.add(Implies(meet[person], start_vars[person] >= ps["avail_start"]))
    opt.add(Implies(meet[person], end_vars[person] <= ps["avail_end"]))
    opt.add(Implies(meet[person], end_vars[person] - start_vars[person] >= ps["min_dur"]))

    # If not meeting, pin times to 0 to avoid spurious times
    opt.add(Implies(Not(meet[person]), start_vars[person] == 0))
    opt.add(Implies(Not(meet[person]), end_vars[person] == 0))

    # Feasible from the day's start location/time
    # You cannot start earlier than arriving directly from the start location
    opt.add(Implies(meet[person], start_vars[person] >= start_time + t(start_location, loc)))

# Pairwise non-overlap with travel-time disjunctions
persons = list(people.keys())
for i in range(len(persons)):
    for j in range(i + 1, len(persons)):
        a = persons[i]
        b = persons[j]
        la = people[a]["location"]
        lb = people[b]["location"]
        # If both meetings occur, either A before B with travel or B before A with travel
        opt.add(Implies(And(meet[a], meet[b]),
                        Or(end_vars[a] + t(la, lb) <= start_vars[b],
                           end_vars[b] + t(lb, la) <= start_vars[a])))

# Objectives:
# 1) Maximize number of people met
sum_meets = Sum([If(meet[p], 1, 0) for p in persons])
h1 = opt.maximize(sum_meets)

# 2) Maximize total meeting minutes
total_meeting_minutes = Sum([If(meet[p], end_vars[p] - start_vars[p], 0) for p in persons])
h2 = opt.maximize(total_meeting_minutes)

# 3) Minimize latest end time (tie-breaker)
latest_end = Int("latest_end")
opt.add(latest_end >= 0)
for p in persons:
    opt.add(latest_end >= end_vars[p])
h3 = opt.minimize(latest_end)

# Solve
if opt.check() != sat:
    print(json.dumps({"itinerary": []}))
else:
    model = opt.model()

    # Collect chosen meetings
    meetings = []
    for p in persons:
        if is_true(model.eval(meet[p])):
            s = model.eval(start_vars[p]).as_long()
            e = model.eval(end_vars[p]).as_long()
            meetings.append({
                "action": "meet",
                "location": people[p]["location"],
                "person": p,
                "start_time": min_to_time(s),
                "end_time": min_to_time(e),
                "start_min": s  # for sorting then removed
            })

    # Sort by start time
    meetings.sort(key=lambda x: x["start_min"])
    for m in meetings:
        del m["start_min"]

    result = {"itinerary": meetings}
    print(json.dumps(result, ensure_ascii=False))