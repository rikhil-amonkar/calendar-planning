# Solve the SF day scheduling problem with Z3
# Objective: maximize number of friends met while respecting availability,
# minimum meeting durations, and inter-location travel times (including start at Russian Hill 09:00).

from z3 import Optimize, Int, Bool, And, Or, Implies, If, Sum

def minutes(hhmm):
    hh, mm = map(int, hhmm.split(":"))
    return hh * 60 + mm

def to_hhmm(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

# Locations
RH = "Russian Hill"
NH = "Nob Hill"
MD = "Mission District"
E  = "Embarcadero"

# Directed travel times (minutes)
travel = {
    (RH, NH): 5,  (RH, MD): 16, (RH, E): 8,
    (NH, RH): 5,  (NH, MD): 13, (NH, E): 9,
    (MD, RH): 15, (MD, NH): 12, (MD, E): 19,
    (E, RH): 8,   (E, NH): 10,  (E, MD): 20,
}

def t(a, b):
    return travel[(a, b)]

# Meetings (including dummy start node)
# name, location, window_start, window_end, min_duration, must_attend
meetings = [
    {"name": "Start",    "loc": RH, "ws": minutes("09:00"), "we": minutes("09:00"), "min": 0,   "fixed": True},
    {"name": "Timothy",  "loc": E,  "ws": minutes("09:45"), "we": minutes("17:45"), "min": 120, "fixed": False},
    {"name": "Patricia", "loc": NH, "ws": minutes("18:30"), "we": minutes("21:45"), "min": 90,  "fixed": False},
    {"name": "Ashley",   "loc": MD, "ws": minutes("20:30"), "we": minutes("21:15"), "min": 45,  "fixed": False},
]

n = len(meetings)

opt = Optimize()

start_vars = []
end_vars = []
attend_vars = []

for i, m in enumerate(meetings):
    s = Int(f"s_{i}")
    e = Int(f"e_{i}")
    start_vars.append(s)
    end_vars.append(e)
    if m["fixed"]:
        # Must attend Start, fixed time equal to window start/end
        opt.add(s == m["ws"])
        opt.add(e == m["we"])
        attend = Bool(f"a_{i}")
        opt.add(attend == True)
        attend_vars.append(attend)
    else:
        attend = Bool(f"a_{i}")
        attend_vars.append(attend)
        # If attending, respect availability and min duration
        opt.add(Implies(attend, And(s >= m["ws"], e <= m["we"], e - s >= m["min"])))
        # If not attending, collapse to availability start (arbitrary but consistent)
        opt.add(Implies(~attend, And(s == m["ws"], e == m["ws"])))

# Pairwise non-overlap with travel time when both attended
for i in range(n):
    for j in range(i + 1, n):
        li = meetings[i]["loc"]
        lj = meetings[j]["loc"]
        # Only meaningful if both are attended
        opt.add(Implies(And(attend_vars[i], attend_vars[j]),
                        Or(start_vars[j] >= end_vars[i] + t(li, lj),
                           start_vars[i] >= end_vars[j] + t(lj, li)) ))

# Primary objective: maximize number of non-dummy meetings attended
friend_attends = [attend_vars[i] for i in range(1, n)]
opt.maximize(Sum([If(a, 1, 0) for a in friend_attends]))

# Secondary objectives (lexicographic):
# - minimize total meeting time (prefer minimum durations)
opt.minimize(Sum([If(attend_vars[i], end_vars[i] - start_vars[i], 0) for i in range(1, n)]))
# - minimize sum of start times (prefer earlier starts)
opt.minimize(Sum([If(attend_vars[i], start_vars[i], 0) for i in range(1, n)]))

# Solve
if opt.check() != sat:
    raise RuntimeError("No feasible schedule found")

model = opt.model()

# Extract attended meetings except Start
solution = []
for i in range(1, n):
    if model.evaluate(attend_vars[i]).is_true():
        s = model.evaluate(start_vars[i]).as_long()
        e = model.evaluate(end_vars[i]).as_long()
        solution.append({
            "action": "meet",
            "person": meetings[i]["name"],
            "start_time": to_hhmm(s),
            "end_time": to_hhmm(e)
        })

# Sort by start time
solution.sort(key=lambda x: x["start_time"])

# Print JSON itinerary
import json
print(json.dumps({"itinerary": solution}))