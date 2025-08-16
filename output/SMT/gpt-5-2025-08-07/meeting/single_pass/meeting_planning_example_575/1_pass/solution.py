# Requires: z3-solver
# pip install z3-solver

from z3 import Optimize, Int, Bool, If, And, Or, Not, Xor, Implies
import json

def mm(h, m):
    return 60*h + m

def fmt(t):
    h = t // 60
    m = t % 60
    return f"{h:02d}:{m:02d}"

# Locations and friends
CASTRO = "The Castro"

friends = {
    "Rebecca": {
        "location": "Presidio",
        "start": mm(18, 15),
        "end": mm(20, 45),
        "min_dur": 60
    },
    "Linda": {
        "location": "Sunset District",
        "start": mm(15, 30),
        "end": mm(19, 45),
        "min_dur": 30
    },
    "Elizabeth": {
        "location": "Haight-Ashbury",
        "start": mm(17, 15),
        "end": mm(19, 30),
        "min_dur": 105
    },
    "William": {
        "location": "Mission District",
        "start": mm(13, 15),
        "end": mm(19, 30),
        "min_dur": 30
    },
    "Robert": {
        "location": "Golden Gate Park",
        "start": mm(14, 15),
        "end": mm(21, 30),
        "min_dur": 45
    },
    "Mark": {
        "location": "Russian Hill",
        "start": mm(10, 0),
        "end": mm(21, 15),
        "min_dur": 75
    }
}

# Travel times (minutes) as given (directional)
T = {}
def add(o, d, t):
    T[(o, d)] = t

# The Castro to ...
add("The Castro", "Presidio", 20)
add("The Castro", "Sunset District", 17)
add("The Castro", "Haight-Ashbury", 6)
add("The Castro", "Mission District", 7)
add("The Castro", "Golden Gate Park", 11)
add("The Castro", "Russian Hill", 18)

# Presidio to ...
add("Presidio", "The Castro", 21)
add("Presidio", "Sunset District", 15)
add("Presidio", "Haight-Ashbury", 15)
add("Presidio", "Mission District", 26)
add("Presidio", "Golden Gate Park", 12)
add("Presidio", "Russian Hill", 14)

# Sunset District to ...
add("Sunset District", "The Castro", 17)
add("Sunset District", "Presidio", 16)
add("Sunset District", "Haight-Ashbury", 15)
add("Sunset District", "Mission District", 24)
add("Sunset District", "Golden Gate Park", 11)
add("Sunset District", "Russian Hill", 24)

# Haight-Ashbury to ...
add("Haight-Ashbury", "The Castro", 6)
add("Haight-Ashbury", "Presidio", 15)
add("Haight-Ashbury", "Sunset District", 15)
add("Haight-Ashbury", "Mission District", 11)
add("Haight-Ashbury", "Golden Gate Park", 7)
add("Haight-Ashbury", "Russian Hill", 17)

# Mission District to ...
add("Mission District", "The Castro", 7)
add("Mission District", "Presidio", 25)
add("Mission District", "Sunset District", 24)
add("Mission District", "Haight-Ashbury", 12)
add("Mission District", "Golden Gate Park", 17)
add("Mission District", "Russian Hill", 15)

# Golden Gate Park to ...
add("Golden Gate Park", "The Castro", 13)
add("Golden Gate Park", "Presidio", 11)
add("Golden Gate Park", "Sunset District", 10)
add("Golden Gate Park", "Haight-Ashbury", 7)
add("Golden Gate Park", "Mission District", 17)
add("Golden Gate Park", "Russian Hill", 19)

# Russian Hill to ...
add("Russian Hill", "The Castro", 21)
add("Russian Hill", "Presidio", 14)
add("Russian Hill", "Sunset District", 23)
add("Russian Hill", "Haight-Ashbury", 17)
add("Russian Hill", "Mission District", 16)
add("Russian Hill", "Golden Gate Park", 21)

def travel(o, d):
    return T[(o, d)]

# Day starts at The Castro, 09:00
day_start = mm(9, 0)

names = list(friends.keys())

opt = Optimize()

meet = {p: Bool(f"meet_{p}") for p in names}
start = {p: Int(f"start_{p}") for p in names}
end = {p: Int(f"end_{p}") for p in names}

# Time window and duration constraints
for p in names:
    info = friends[p]
    s, e, dur = info["start"], info["end"], info["min_dur"]
    # If we meet, must be within window and meet min duration
    opt.add(Implies(meet[p], And(start[p] >= s,
                                 end[p] == start[p] + dur,
                                 end[p] <= e)))
    # Vars non-negative
    opt.add(start[p] >= 0)
    opt.add(end[p] >= 0)
    # Initial travel from Castro to first/any meeting
    opt.add(Implies(meet[p], start[p] >= day_start + travel(CASTRO, info["location"])))

# Sequencing constraints with travel times (disjunctive scheduling)
order = {}
for i in range(len(names)):
    for j in range(i+1, len(names)):
        a, b = names[i], names[j]
        order[(a,b)] = Bool(f"order_{a}_before_{b}")
        order[(b,a)] = Bool(f"order_{b}_before_{a}")

        # If both are met, exactly one must be before the other
        opt.add(Implies(And(meet[a], meet[b]), Xor(order[(a,b)], order[(b,a)])))
        # Order vars can only be true if both are met
        opt.add(Implies(order[(a,b)], And(meet[a], meet[b])))
        opt.add(Implies(order[(b,a)], And(meet[a], meet[b])))

        # If a before b, include travel time a->b
        oa_loc = friends[a]["location"]
        ob_loc = friends[b]["location"]
        ta = friends[a]["min_dur"]
        tb = friends[b]["min_dur"]  # not used directly here

        opt.add(Implies(order[(a,b)],
                        start[b] >= end[a] + travel(oa_loc, ob_loc)))
        opt.add(Implies(order[(b,a)],
                        start[a] >= end[b] + travel(ob_loc, oa_loc)))

# Objective: maximize number of friends met
obj = sum([If(meet[p], 1, 0) for p in names])
opt.maximize(obj)

# Optionally, as a tie-breaker, minimize latest end time to encourage earlier finishes
latest_end = Int("latest_end")
opt.add(latest_end >= 0)
for p in names:
    opt.add(Implies(meet[p], latest_end >= end[p]))
opt.minimize(latest_end)

assert opt.check().r == 1, "Solver failed to find a solution"
m = opt.model()

schedule = []
for p in names:
    if m.evaluate(meet[p], model_completion=True):
        st = m.evaluate(start[p]).as_long()
        en = m.evaluate(end[p]).as_long()
        schedule.append({
            "action": "meet",
            "person": p,
            "start_time": fmt(st),
            "end_time": fmt(en)
        })

# Sort by start time
schedule.sort(key=lambda x: x["start_time"])

print(json.dumps({"itinerary": schedule}))