from z3 import Optimize, Int, Bool, If, Or, And, Sum
import json

# Helper to convert HH:MM to minutes since midnight
def hhmm_to_min(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

# Helper to convert minutes since midnight to HH:MM
def min_to_hhmm(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

# Data
locations = {
    "Charles": "Alamo Square",
    "Margaret": "Russian Hill",
    "Daniel": "Golden Gate Park",
    "Stephanie": "Mission District",
}

availability = {
    "Charles":   (hhmm_to_min("18:00"), hhmm_to_min("20:45")),
    "Margaret":  (hhmm_to_min("09:00"), hhmm_to_min("16:00")),
    "Daniel":    (hhmm_to_min("08:00"), hhmm_to_min("13:30")),
    "Stephanie": (hhmm_to_min("20:30"), hhmm_to_min("22:00")),
}

min_durations = {
    "Charles": 90,
    "Margaret": 30,
    "Daniel": 15,
    "Stephanie": 90,
}

# Directed travel times (minutes)
travel = {
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Mission District"): 24,

    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Mission District"): 10,

    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Mission District"): 16,

    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Alamo Square"): 10,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Mission District"): 17,

    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Golden Gate Park"): 17,
}

friends = list(locations.keys())
start_location = "Sunset District"
arrival_time = hhmm_to_min("09:00")

# Z3 model
opt = Optimize()
opt.set(priority='lex')  # maximize number of meetings, then secondary objectives lexicographically

s_vars = {f: Int(f"s_{f}") for f in friends}   # start time
d_vars = {f: Int(f"d_{f}") for f in friends}   # duration
meet_vars = {f: Bool(f"meet_{f}") for f in friends}

for f in friends:
    s = s_vars[f]
    d = d_vars[f]
    meet = meet_vars[f]
    loc = locations[f]
    a_start, a_end = availability[f]
    min_d = min_durations[f]

    # Base domain constraints
    opt.add(s >= 0, d >= 0)

    # If meeting, respect availability, minimum duration, and reachable from start
    opt.add(Or(
        meet == False,
        And(
            s >= a_start,
            s + d <= a_end,
            d >= min_d,
            # Must be reachable from the day's starting point at least
            s >= arrival_time + travel[(start_location, loc)]
        )
    ))

    # If not meeting, set duration to 0 to avoid affecting objectives
    opt.add(Or(meet, d == 0))

# Pairwise non-overlap with travel times (disjunctive constraints)
for i in range(len(friends)):
    for j in range(i + 1, len(friends)):
        fi = friends[i]
        fj = friends[j]
        si, di, mi = s_vars[fi], d_vars[fi], meet_vars[fi]
        sj, dj, mj = s_vars[fj], d_vars[fj], meet_vars[fj]
        li, lj = locations[fi], locations[fj]
        tij = travel[(li, lj)]
        tji = travel[(lj, li)]
        # If meet both, then either i before j or j before i with travel time
        opt.add(Or(
            Or(mi == False, mj == False),
            Or(si + di + tij <= sj, sj + dj + tji <= si)
        ))

# Objectives:
# 1) Maximize number of friends met
count_met = Sum([If(meet_vars[f], 1, 0) for f in friends])
opt.maximize(count_met)

# 2) Minimize total meeting duration (prefer minimum durations)
opt.minimize(Sum([If(meet_vars[f], d_vars[f], 0) for f in friends]))

# 3) Minimize sum of start times (prefer earlier feasible starts)
opt.minimize(Sum([If(meet_vars[f], s_vars[f], 0) for f in friends]))

# Solve
if opt.check() != None:
    model = opt.model()
    schedule = []
    for f in friends:
        if model.eval(meet_vars[f]):
            s = model.eval(s_vars[f]).as_long()
            d = model.eval(d_vars[f]).as_long()
            e = s + d
            schedule.append({
                "action": "meet",
                "person": f,
                "start_time": min_to_hhmm(s),
                "end_time": min_to_hhmm(e),
            })
    # Sort by start_time
    schedule.sort(key=lambda x: x["start_time"])
    # Output JSON itinerary
    print(json.dumps({"itinerary": schedule}, ensure_ascii=False))
else:
    print(json.dumps({"itinerary": []}, ensure_ascii=False))