"""SOLUTION:"""
import json
from z3 import Optimize, Int, Bool, If, And, Or, Implies

# Helper to convert hours and minutes to minutes since midnight
def hm(h, m):
    return h * 60 + m

# Helper to format minutes since midnight to "H:MM" 24-hour format without leading zero for hour
def minutes_to_str(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Travel times (in minutes), directed
dist = {
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

# Start info
start_location = "Sunset District"
start_time = hm(9, 0)

# Friends data
friends = [
    {
        "name": "Charles",
        "location": "Alamo Square",
        "window_start": hm(18, 0),
        "window_end": hm(20, 45),
        "min_duration": 90
    },
    {
        "name": "Margaret",
        "location": "Russian Hill",
        "window_start": hm(9, 0),
        "window_end": hm(16, 0),
        "min_duration": 30
    },
    {
        "name": "Daniel",
        "location": "Golden Gate Park",
        "window_start": hm(8, 0),
        "window_end": hm(13, 30),
        "min_duration": 15
    },
    {
        "name": "Stephanie",
        "location": "Mission District",
        "window_start": hm(20, 30),
        "window_end": hm(22, 0),
        "min_duration": 90
    },
]

# Create optimization model
opt = Optimize()

# Variables per friend
vars_map = {}
for f in friends:
    name = f["name"]
    s = Int(f"s_{name}")      # start time (minutes since midnight)
    d = Int(f"d_{name}")      # duration
    e = Int(f"e_{name}")      # end time
    meet = Bool(f"meet_{name}")  # whether we meet them

    # Domains
    opt.add(s >= 0, s <= 24 * 60)
    opt.add(d >= 0, d <= 24 * 60)
    opt.add(e == s + d)

    # If we meet, duration equals minimum required, and schedule must lie within availability
    min_dur = f["min_duration"]
    ws = f["window_start"]
    we = f["window_end"]
    loc = f["location"]

    opt.add(d == If(meet, min_dur, 0))
    # Window constraints only if met
    opt.add(Implies(meet, And(s >= ws, e <= we, s <= we - min_dur)))
    # Starting location travel feasibility: if met, cannot start before we can travel from starting point
    opt.add(Implies(meet, s >= start_time + dist[(start_location, loc)]))

    vars_map[name] = {"s": s, "d": d, "e": e, "meet": meet}

# Pairwise non-overlap with travel times
for i in range(len(friends)):
    for j in range(i + 1, len(friends)):
        fi = friends[i]
        fj = friends[j]
        ni, nj = fi["name"], fj["name"]
        li, lj = fi["location"], fj["location"]

        before_ij = Bool(f"before_{ni}_{nj}")

        # If both meetings occur, then either i before j (plus travel), or j before i (plus travel)
        opt.add(
            Implies(
                And(vars_map[ni]["meet"], vars_map[nj]["meet"]),
                Or(
                    And(
                        before_ij,
                        vars_map[ni]["e"] + dist[(li, lj)] <= vars_map[nj]["s"]
                    ),
                    And(
                        Not(before_ij),
                        vars_map[nj]["e"] + dist[(lj, li)] <= vars_map[ni]["s"]
                    )
                )
            )
        )

# Objective: maximize number of friends met
total_met = sum([If(vars_map[f["name"]]["meet"], 1, 0) for f in friends])
opt.maximize(total_met)

# Secondary objective: minimize makespan (latest finishing time among met)
makespan = Int("makespan")
opt.add(makespan >= 0)
for f in friends:
    e = vars_map[f["name"]]["e"]
    meet = vars_map[f["name"]]["meet"]
    # If met, makespan >= e
    opt.add(Implies(meet, makespan >= e))
opt.minimize(makespan)

# Solve
if opt.check() != 1:
    # No solution; output empty itinerary
    result = {"itinerary": []}
    print(json.dumps(result))
    raise SystemExit

m = opt.model()

# Build itinerary
events = []
for f in friends:
    name = f["name"]
    loc = f["location"]
    meet = m.evaluate(vars_map[name]["meet"])
    if str(meet) == "true":
        s = m.evaluate(vars_map[name]["s"]).as_long()
        e = m.evaluate(vars_map[name]["e"]).as_long()
        events.append({
            "action": "meet",
            "location": loc,
            "person": name,
            "start_time": minutes_to_str(s),
            "end_time": minutes_to_str(e),
        })

# Sort by start time
events.sort(key=lambda x: (int(x["start_time"].split(":")[0]) * 60 + int(x["start_time"].split(":")[1])))

result = {"itinerary": events}
print(json.dumps(result, ensure_ascii=False))