# Requires: pip install z3-solver
from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum

def t(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

# Data
origin = "Haight-Ashbury"
origin_time = t("09:00")

locations = {
    "Sarah":  "Fisherman's Wharf",
    "Mary":   "Richmond District",
    "Helen":  "Mission District",
    "Thomas": "Bayview",
}

windows = {
    "Sarah":  (t("14:45"), t("17:30")),
    "Mary":   (t("13:00"), t("19:15")),
    "Helen":  (t("21:45"), t("22:30")),
    "Thomas": (t("15:15"), t("18:45")),
}

min_durations = {
    "Sarah": 105,
    "Mary":   75,
    "Helen":  30,
    "Thomas":120,
}

# Travel times (minutes), directional
travel = {}
def set_travel(a,b,mins):
    travel[(a,b)] = mins

set_travel("Haight-Ashbury", "Fisherman's Wharf", 23)
set_travel("Haight-Ashbury", "Richmond District", 10)
set_travel("Haight-Ashbury", "Mission District", 11)
set_travel("Haight-Ashbury", "Bayview", 18)

set_travel("Fisherman's Wharf", "Haight-Ashbury", 22)
set_travel("Fisherman's Wharf", "Richmond District", 18)
set_travel("Fisherman's Wharf", "Mission District", 22)
set_travel("Fisherman's Wharf", "Bayview", 26)

set_travel("Richmond District", "Haight-Ashbury", 10)
set_travel("Richmond District", "Fisherman's Wharf", 18)
set_travel("Richmond District", "Mission District", 20)
set_travel("Richmond District", "Bayview", 26)

set_travel("Mission District", "Haight-Ashbury", 12)
set_travel("Mission District", "Fisherman's Wharf", 22)
set_travel("Mission District", "Richmond District", 20)
set_travel("Mission District", "Bayview", 15)

set_travel("Bayview", "Haight-Ashbury", 19)
set_travel("Bayview", "Fisherman's Wharf", 25)
set_travel("Bayview", "Richmond District", 25)
set_travel("Bayview", "Mission District", 13)

friends = list(locations.keys())

# Z3 model
opt = Optimize()

start = {f: Int(f"start_{f}") for f in friends}
end   = {f: Int(f"end_{f}")   for f in friends}
meet  = {f: Bool(f"meet_{f}") for f in friends}

# Bounds and availability constraints
DAY_END = 24*60
for f in friends:
    s = start[f]; e = end[f]; m = meet[f]
    avail_s, avail_e = windows[f]
    # time domain
    opt.add(And(s >= 0, s <= DAY_END, e >= 0, e <= DAY_END))
    # If meeting, enforce within window, duration, and origin reachability
    loc = locations[f]
    opt.add(If(m,
               And(s >= avail_s,
                   e <= avail_e,
                   e - s >= min_durations[f],
                   s >= origin_time + travel[(origin, loc)]),
               And(e == e, s == s)))  # no-op when not meeting

# Travel feasibility between meetings (no overlap + travel time)
for i in range(len(friends)):
    for j in range(i+1, len(friends)):
        fi, fj = friends[i], friends[j]
        li, lj = locations[fi], locations[fj]
        # If both meetings happen, either fi before fj with travel time, or fj before fi with travel time
        opt.add(If(And(meet[fi], meet[fj]),
                   Or(end[fi] + travel[(li, lj)] <= start[fj],
                      end[fj] + travel[(lj, li)] <= start[fi]),
                   True))

# Objectives:
# 1) Maximize number of friends met
num_met = Sum([If(meet[f], 1, 0) for f in friends])
opt.maximize(num_met)

# 2) Maximize total meeting time
total_meeting_time = Sum([If(meet[f], end[f] - start[f], 0) for f in friends])
opt.maximize(total_meeting_time)

# 3) Break ties by preferring earlier start times overall
sum_start_times = Sum([If(meet[f], start[f], 0) for f in friends])
opt.minimize(sum_start_times)

# Solve
if opt.check() != sat:
    raise RuntimeError("No feasible schedule found")

model = opt.model()

# Collect itinerary
itinerary = []
for f in friends:
    if model.evaluate(meet[f], model_completion=True):
        s = model.evaluate(start[f]).as_long()
        e = model.evaluate(end[f]).as_long()
        def to_hhmm(x):
            hh = x // 60
            mm = x % 60
            return f"{hh:02d}:{mm:02d}"
        itinerary.append({
            "action": "meet",
            "person": f,
            "start_time": to_hhmm(s),
            "end_time": to_hhmm(e),
        })

# Sort by start time
itinerary.sort(key=lambda x: x["start_time"])

# Print JSON as specified
import json
print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))