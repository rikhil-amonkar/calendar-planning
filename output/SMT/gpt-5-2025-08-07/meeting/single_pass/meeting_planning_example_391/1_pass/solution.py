# Solve the SF friend-meeting schedule with Z3 Optimize
# Objective: maximize number of friends met subject to availability, minimum durations, and travel times.

from z3 import Int, Bool, If, Or, And, Optimize, sat
import json

def to_minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return 60*h + m

def fmt(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Data
Sunset = "Sunset District"

friends = {
    "Kevin":    {"loc": "Alamo Square",      "open": to_minutes("08:15"), "close": to_minutes("21:30"), "min_dur": 75},
    "Kimberly": {"loc": "Russian Hill",      "open": to_minutes("08:45"), "close": to_minutes("12:30"), "min_dur": 30},
    "Joseph":   {"loc": "Presidio",          "open": to_minutes("18:30"), "close": to_minutes("19:15"), "min_dur": 45},
    "Thomas":   {"loc": "Financial District","open": to_minutes("19:00"), "close": to_minutes("21:45"), "min_dur": 45},
}

# Directed travel times in minutes
travel = {
    ( "Sunset District", "Alamo Square"): 17,
    ( "Sunset District", "Russian Hill"): 24,
    ( "Sunset District", "Presidio"): 16,
    ( "Sunset District", "Financial District"): 30,

    ( "Alamo Square", "Sunset District"): 16,
    ( "Alamo Square", "Russian Hill"): 13,
    ( "Alamo Square", "Presidio"): 18,
    ( "Alamo Square", "Financial District"): 17,

    ( "Russian Hill", "Sunset District"): 23,
    ( "Russian Hill", "Alamo Square"): 15,
    ( "Russian Hill", "Presidio"): 14,
    ( "Russian Hill", "Financial District"): 11,

    ( "Presidio", "Sunset District"): 15,
    ( "Presidio", "Alamo Square"): 18,
    ( "Presidio", "Russian Hill"): 14,
    ( "Presidio", "Financial District"): 23,

    ( "Financial District", "Sunset District"): 31,
    ( "Financial District", "Alamo Square"): 17,
    ( "Financial District", "Russian Hill"): 10,
    ( "Financial District", "Presidio"): 22,
}

start_loc = Sunset
start_time = to_minutes("09:00")

P = list(friends.keys())

opt = Optimize()

# Decision variables
start = {p: Int(f"start_{p}") for p in P}
end   = {p: Int(f"end_{p}")   for p in P}
meet  = {p: Bool(f"meet_{p}") for p in P}

# Bounds and availability constraints
for p in P:
    info = friends[p]
    dur = info["min_dur"]
    # Time domain
    opt.add(start[p] >= 0, start[p] <= 24*60)
    opt.add(end[p]   >= 0, end[p]   <= 24*60)
    # Duration
    opt.add(end[p] == start[p] + dur)
    # Within availability if meeting
    opt.add(Or(
        meet[p] == False,
        And(start[p] >= info["open"], end[p] <= info["close"])
    ))
    # Cannot start before earliest arrival from origin (safe lower bound)
    origin_travel = travel[(start_loc, info["loc"])]
    opt.add(start[p] >= start_time + origin_travel)

# Pairwise non-overlap with travel times (disjunctive)
for i in range(len(P)):
    for j in range(i+1, len(P)):
        p, q = P[i], P[j]
        tpq = travel[(friends[p]["loc"], friends[q]["loc"])]
        tqp = travel[(friends[q]["loc"], friends[p]["loc"])]
        opt.add(Or(
            meet[p] == False,
            meet[q] == False,
            end[p] + tpq <= start[q],
            end[q] + tqp <= start[p]
        ))

# Last end (makespan) among met meetings
last_end = Int("last_end")
opt.add(last_end >= 0, last_end <= 24*60)
for p in P:
    opt.add(Or(meet[p] == False, end[p] <= last_end))

# Objective 1: maximize number of friends met
total_met = sum(If(meet[p], 1, 0) for p in P)
opt.maximize(total_met)

# Objective 2: minimize makespan (finish earlier in the day)
opt.minimize(last_end)

# Objective 3: minimize sum of start times for determinism (prefer earlier starts)
sum_starts = sum(If(meet[p], start[p], 0) for p in P)
opt.minimize(sum_starts)

# Solve
if opt.check() != sat:
    # Fallback: no solution
    print(json.dumps({"itinerary": []}))
    raise SystemExit(0)

m = opt.model()

# Extract meetings
meetings = []
for p in P:
    if m.eval(meet[p]).is_true():
        s = m.eval(start[p]).as_long()
        e = m.eval(end[p]).as_long()
        meetings.append({
            "action": "meet",
            "person": p,
            "start_time": fmt(s),
            "end_time": fmt(e),
        })

# Sort by start time
meetings.sort(key=lambda x: x["start_time"])

print(json.dumps({"itinerary": meetings}))