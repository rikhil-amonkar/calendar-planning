# SOLUTION (fixed import):
import json
from z3 import Optimize, Int, Bool, If, And, Or, Implies, Sum, Not, is_true, sat

# Time utility
def minutes(h, m):
    return h * 60 + m

def format_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Start location and time
start_location = "The Castro"
start_time = minutes(9, 0)

# Travel times (in minutes), directed
travel = {}
def set_travel(a, b, t):
    travel[(a, b)] = t

places = [
    "The Castro",
    "Presidio",
    "Sunset District",
    "Haight-Ashbury",
    "Mission District",
    "Golden Gate Park",
    "Russian Hill",
]

# Populate travel times from the problem statement
set_travel("The Castro", "Presidio", 20)
set_travel("The Castro", "Sunset District", 17)
set_travel("The Castro", "Haight-Ashbury", 6)
set_travel("The Castro", "Mission District", 7)
set_travel("The Castro", "Golden Gate Park", 11)
set_travel("The Castro", "Russian Hill", 18)

set_travel("Presidio", "The Castro", 21)
set_travel("Presidio", "Sunset District", 15)
set_travel("Presidio", "Haight-Ashbury", 15)
set_travel("Presidio", "Mission District", 26)
set_travel("Presidio", "Golden Gate Park", 12)
set_travel("Presidio", "Russian Hill", 14)

set_travel("Sunset District", "The Castro", 17)
set_travel("Sunset District", "Presidio", 16)
set_travel("Sunset District", "Haight-Ashbury", 15)
set_travel("Sunset District", "Mission District", 24)
set_travel("Sunset District", "Golden Gate Park", 11)
set_travel("Sunset District", "Russian Hill", 24)

set_travel("Haight-Ashbury", "The Castro", 6)
set_travel("Haight-Ashbury", "Presidio", 15)
set_travel("Haight-Ashbury", "Sunset District", 15)
set_travel("Haight-Ashbury", "Mission District", 11)
set_travel("Haight-Ashbury", "Golden Gate Park", 7)
set_travel("Haight-Ashbury", "Russian Hill", 17)

set_travel("Mission District", "The Castro", 7)
set_travel("Mission District", "Presidio", 25)
set_travel("Mission District", "Sunset District", 24)
set_travel("Mission District", "Haight-Ashbury", 12)
set_travel("Mission District", "Golden Gate Park", 17)
set_travel("Mission District", "Russian Hill", 15)

set_travel("Golden Gate Park", "The Castro", 13)
set_travel("Golden Gate Park", "Presidio", 11)
set_travel("Golden Gate Park", "Sunset District", 10)
set_travel("Golden Gate Park", "Haight-Ashbury", 7)
set_travel("Golden Gate Park", "Mission District", 17)
set_travel("Golden Gate Park", "Russian Hill", 19)

set_travel("Russian Hill", "The Castro", 21)
set_travel("Russian Hill", "Presidio", 14)
set_travel("Russian Hill", "Sunset District", 23)
set_travel("Russian Hill", "Haight-Ashbury", 17)
set_travel("Russian Hill", "Mission District", 16)
set_travel("Russian Hill", "Golden Gate Park", 21)

# Friends and their constraints
friends = {
    "Rebecca": {
        "location": "Presidio",
        "avail_start": minutes(18, 15),
        "avail_end": minutes(20, 45),
        "min_meet": 60
    },
    "Linda": {
        "location": "Sunset District",
        "avail_start": minutes(15, 30),
        "avail_end": minutes(19, 45),
        "min_meet": 30
    },
    "Elizabeth": {
        "location": "Haight-Ashbury",
        "avail_start": minutes(17, 15),
        "avail_end": minutes(19, 30),
        "min_meet": 105
    },
    "William": {
        "location": "Mission District",
        "avail_start": minutes(13, 15),
        "avail_end": minutes(19, 30),
        "min_meet": 30
    },
    "Robert": {
        "location": "Golden Gate Park",
        "avail_start": minutes(14, 15),
        "avail_end": minutes(21, 30),
        "min_meet": 45
    },
    "Mark": {
        "location": "Russian Hill",
        "avail_start": minutes(10, 0),
        "avail_end": minutes(21, 15),
        "min_meet": 75
    },
}

# Z3 variables
opt = Optimize()
start_vars = {}
end_vars = {}
inc_vars = {}

# Variable domains and availability constraints
for name, info in friends.items():
    s = Int(f"start_{name}")
    e = Int(f"end_{name}")
    inc = Bool(f"inc_{name}")
    start_vars[name] = s
    end_vars[name] = e
    inc_vars[name] = inc

    ws = info["avail_start"]
    we = info["avail_end"]
    min_meet = info["min_meet"]
    loc = info["location"]

    # Domain constraints
    opt.add(And(s >= 0, s <= 24 * 60, e >= 0, e <= 24 * 60))

    # Availability and meeting duration constraints when included
    opt.add(Implies(inc, And(s >= ws, e <= we, e > s, e - s >= min_meet)))

    # Reachability from start location (safe lower bound)
    if (start_location, loc) in travel:
        opt.add(Implies(inc, s >= start_time + travel[(start_location, loc)]))
    else:
        opt.add(Implies(inc, False))

# Non-overlap and travel-time disjunctions between all included meetings
friend_names = list(friends.keys())
for i in range(len(friend_names)):
    for j in range(i + 1, len(friend_names)):
        fi = friend_names[i]
        fj = friend_names[j]
        li = friends[fi]["location"]
        lj = friends[fj]["location"]
        tij = travel[(li, lj)]
        tji = travel[(lj, li)]
        si, ei, inci = start_vars[fi], end_vars[fi], inc_vars[fi]
        sj, ej, incj = start_vars[fj], end_vars[fj], inc_vars[fj]
        opt.add(Or(
            Not(inci), Not(incj),
            ei + tij <= sj,
            ej + tji <= si
        ))

# Objectives:
# 1) Maximize number of friends met
num_met = Sum([If(inc_vars[n], 1, 0) for n in friend_names])
opt.maximize(num_met)
# 2) Maximize total meeting minutes (secondary)
total_minutes = Sum([If(inc_vars[n], end_vars[n] - start_vars[n], 0) for n in friend_names])
opt.maximize(total_minutes)

# Solve
if opt.check() != sat:
    print(json.dumps({"itinerary": []}))
else:
    m = opt.model()
    itinerary = []
    for n in friend_names:
        if is_true(m.eval(inc_vars[n])):
            start_t = m.eval(start_vars[n]).as_long()
            end_t = m.eval(end_vars[n]).as_long()
            itinerary.append({
                "action": "meet",
                "location": friends[n]["location"],
                "person": n,
                "start_time": format_time(start_t),
                "end_time": format_time(end_t),
            })
    itinerary.sort(key=lambda x: (int(x["start_time"].split(":")[0]) * 60 + int(x["start_time"].split(":")[1])))
    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))