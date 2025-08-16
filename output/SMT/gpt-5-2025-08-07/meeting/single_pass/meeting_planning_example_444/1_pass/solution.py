# Z3-based solver for the SF day scheduling problem.
# It maximizes the number of friends met while observing availability, minimum meeting durations, and travel times.

from z3 import *
import json

# Time helper functions
def to_minutes(h, m):
    return (h - 9) * 60 + m  # minutes relative to 09:00

def min_to_time(m):
    # Convert minutes since 09:00 to HH:MM 24h format
    total_minutes = 9 * 60 + m
    hh = total_minutes // 60
    mm = total_minutes % 60
    return f"{hh:02d}:{mm:02d}"

# Locations
FD = "Financial District"
RH = "Russian Hill"
SD = "Sunset District"
NB = "North Beach"
TC = "The Castro"
GGP = "Golden Gate Park"

# Directed travel times (minutes)
travel = {
    FD: {RH: 10, SD: 31, NB: 7,  TC: 23, GGP: 23},
    RH: {FD: 11, SD: 23, NB: 5,  TC: 21, GGP: 21},
    SD: {FD: 30, RH: 24, NB: 29, TC: 17, GGP: 11},
    NB: {FD: 8,  RH: 4,  SD: 27, TC: 22, GGP: 22},
    TC: {FD: 20, RH: 18, SD: 17, NB: 20, GGP: 11},
    GGP:{FD: 26, RH: 19, SD: 10, NB: 24, TC: 13},
}

def get_travel(a, b):
    if a == b:
        return 0
    return travel[a][b]

# Friends data
friends = {
    "Ronald":   {"loc": RH,  "win": (to_minutes(13,45), to_minutes(17,15)), "min_dur": 105},
    "Patricia": {"loc": SD,  "win": (to_minutes(9,15),  to_minutes(22,0)),  "min_dur": 60},
    "Laura":    {"loc": NB,  "win": (to_minutes(12,30), to_minutes(12,45)), "min_dur": 15},
    "Emily":    {"loc": TC,  "win": (to_minutes(16,15), to_minutes(18,30)), "min_dur": 60},
    "Mary":     {"loc": GGP, "win": (to_minutes(15,0),  to_minutes(16,30)), "min_dur": 60},
}

names = list(friends.keys())
n = len(names)

# Horizon: from 09:00 to 22:00
H = to_minutes(22, 0)

opt = Optimize()

# Variables
start = {name: Int(f"start_{name}") for name in names}
end   = {name: Int(f"end_{name}")   for name in names}
meet  = {name: Bool(f"meet_{name}") for name in names}

# Base constraints per friend
for name in names:
    s = start[name]
    e = end[name]
    loc = friends[name]["loc"]
    w0, w1 = friends[name]["win"]
    min_dur = friends[name]["min_dur"]

    # Bounds
    opt.add(s >= 0, e >= 0, s <= H, e <= H, e >= s)

    # If meeting, respect availability window, minimum duration, and time to reach from FD
    opt.add(Implies(meet[name], And(
        s >= w0,
        e <= w1,
        e - s >= min_dur,
        s >= get_travel(FD, loc)
    )))

    # If not meeting, zero duration (keeps things simple)
    opt.add(Implies(Not(meet[name]), e == s))

# Pairwise non-overlap with travel times (disjunctive scheduling)
before = {}
for i in range(n):
    for j in range(i+1, n):
        ni, nj = names[i], names[j]
        before[(ni, nj)] = Bool(f"before_{ni}_{nj}")
        bi = before[(ni, nj)]
        li, lj = friends[ni]["loc"], friends[nj]["loc"]
        # If both meetings happen
        opt.add(Implies(And(meet[ni], meet[nj], bi), end[ni] + get_travel(li, lj) <= start[nj]))
        opt.add(Implies(And(meet[ni], meet[nj], Not(bi)), end[nj] + get_travel(lj, li) <= start[ni]))
        # If one or both doesn't happen, no ordering constraint is needed

# Objectives
# 1) Maximize number of friends met
obj_meet_count = Sum([If(meet[name], 1, 0) for name in names])
opt.maximize(obj_meet_count)

# 2) Maximize total meeting time (secondary)
obj_total_duration = Sum([If(meet[name], end[name] - start[name], 0) for name in names])
opt.maximize(obj_total_duration)

# 3) Minimize latest end time (tertiary) to prefer earlier schedules
makespan = Int("makespan")
opt.add(makespan >= 0)
for name in names:
    opt.add(makespan >= end[name])
opt.minimize(makespan)

# Solve
if opt.check() != sat:
    raise RuntimeError("No feasible schedule found.")

model = opt.model()

# Build itinerary (only meetings that occur)
meetings = []
for name in names:
    if is_true(model[meet[name]]):
        s_val = model[start[name]].as_long()
        e_val = model[end[name]].as_long()
        meetings.append({
            "action": "meet",
            "person": name,
            "start_time": min_to_time(s_val),
            "end_time": min_to_time(e_val)
        })

# Sort chronologically by start_time
def time_to_minutes_str(tstr):
    hh, mm = map(int, tstr.split(":"))
    return hh*60 + mm

meetings.sort(key=lambda x: time_to_minutes_str(x["start_time"]))

# Output JSON
print(json.dumps({"itinerary": meetings}, ensure_ascii=False))