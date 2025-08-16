# Solve the SF friend-meeting problem using Z3 Optimize
# Maximizes the number of friends met while respecting travel times and availability windows.

from z3 import *
import json

def to_minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def fmt_minutes(mm):
    h = mm // 60
    m = mm % 60
    return f"{h:02d}:{m:02d}"

# Travel times (minutes), directed, as given
travel = {
    "Pacific Heights": {"Marina District": 6, "The Castro": 16, "Richmond District": 12, "Alamo Square": 10, "Financial District": 13, "Presidio": 11, "Mission District": 15, "Nob Hill": 8, "Russian Hill": 7},
    "Marina District": {"Pacific Heights": 7, "The Castro": 22, "Richmond District": 11, "Alamo Square": 15, "Financial District": 17, "Presidio": 10, "Mission District": 20, "Nob Hill": 12, "Russian Hill": 8},
    "The Castro": {"Pacific Heights": 16, "Marina District": 21, "Richmond District": 16, "Alamo Square": 8, "Financial District": 21, "Presidio": 20, "Mission District": 7, "Nob Hill": 16, "Russian Hill": 18},
    "Richmond District": {"Pacific Heights": 10, "Marina District": 9, "The Castro": 16, "Alamo Square": 13, "Financial District": 22, "Presidio": 7, "Mission District": 20, "Nob Hill": 17, "Russian Hill": 13},
    "Alamo Square": {"Pacific Heights": 10, "Marina District": 15, "The Castro": 8, "Richmond District": 11, "Financial District": 17, "Presidio": 17, "Mission District": 10, "Nob Hill": 11, "Russian Hill": 13},
    "Financial District": {"Pacific Heights": 13, "Marina District": 15, "The Castro": 20, "Richmond District": 21, "Alamo Square": 17, "Presidio": 22, "Mission District": 17, "Nob Hill": 8, "Russian Hill": 11},
    "Presidio": {"Pacific Heights": 11, "Marina District": 11, "The Castro": 21, "Richmond District": 7, "Alamo Square": 19, "Financial District": 23, "Mission District": 26, "Nob Hill": 18, "Russian Hill": 14},
    "Mission District": {"Pacific Heights": 16, "Marina District": 19, "The Castro": 7, "Richmond District": 20, "Alamo Square": 11, "Financial District": 15, "Presidio": 25, "Nob Hill": 12, "Russian Hill": 15},
    "Nob Hill": {"Pacific Heights": 8, "Marina District": 11, "The Castro": 17, "Richmond District": 14, "Alamo Square": 11, "Financial District": 9, "Presidio": 17, "Mission District": 13, "Russian Hill": 5},
    "Russian Hill": {"Pacific Heights": 7, "Marina District": 7, "The Castro": 21, "Richmond District": 14, "Alamo Square": 15, "Financial District": 11, "Presidio": 14, "Mission District": 16, "Nob Hill": 5}
}

# Friends, availability windows (24-hour), min required durations (minutes)
friends = [
    {"name": "Linda",   "loc": "Marina District",   "start": "18:00", "end": "22:00", "min": 30},
    {"name": "Kenneth", "loc": "The Castro",        "start": "14:45", "end": "16:15", "min": 30},
    {"name": "Kimberly","loc": "Richmond District", "start": "14:15", "end": "22:00", "min": 30},
    {"name": "Paul",    "loc": "Alamo Square",      "start": "21:00", "end": "21:30", "min": 15},
    {"name": "Carol",   "loc": "Financial District","start": "10:15", "end": "12:00", "min": 60},
    {"name": "Brian",   "loc": "Presidio",          "start": "10:00", "end": "21:30", "min": 75},
    {"name": "Laura",   "loc": "Mission District",  "start": "16:15", "end": "20:30", "min": 30},
    {"name": "Sandra",  "loc": "Nob Hill",          "start": "09:15", "end": "18:30", "min": 60},
    {"name": "Karen",   "loc": "Russian Hill",      "start": "18:30", "end": "22:00", "min": 75},
]

# Convert time strings to minutes
for f in friends:
    f["s_min"] = to_minutes(f["start"])
    f["e_min"] = to_minutes(f["end"])

start_loc = "Pacific Heights"
start_time_min = to_minutes("09:00")

# Big-M constant
M = 2000

opt = Optimize()

# Variables
meet = {}
start = {}
end = {}
duration = {}
n = len(friends)

for i, f in enumerate(friends):
    meet[i] = Bool(f"meet_{i}")
    start[i] = Int(f"start_{i}")
    duration[i] = IntVal(f["min"])  # fixed to minimum duration
    end[i] = Int(f"end_{i}")

    # Time domain bounds
    opt.add(And(start[i] >= 0, start[i] <= 24*60))
    opt.add(And(end[i] >= 0, end[i] <= 24*60))

    # Define end time
    opt.add(end[i] == start[i] + f["min"])

    # Availability window constraints only if meeting them
    opt.add(Implies(meet[i], And(start[i] >= f["s_min"], end[i] <= f["e_min"])))

    # Must be reachable from start (if met)
    t_from_start = travel[start_loc][f["loc"]]
    opt.add(Implies(meet[i], start[i] >= start_time_min + t_from_start))

# Pairwise ordering constraints
order = {}
for i in range(n):
    for j in range(i+1, n):
        oij = Bool(f"o_{i}_before_{j}")
        oji = Bool(f"o_{j}_before_{i}")
        order[(i,j)] = (oij, oji)

        # If an order variable is true, both meetings must occur
        opt.add(Implies(oij, And(meet[i], meet[j])))
        opt.add(Implies(oji, And(meet[i], meet[j])))

        # Travel time constraints under that order
        ti_to_j = travel[friends[i]["loc"]][friends[j]["loc"]]
        tj_to_i = travel[friends[j]["loc"]][friends[i]["loc"]]
        opt.add(Implies(oij, start[j] >= end[i] + ti_to_j))
        opt.add(Implies(oji, start[i] >= end[j] + tj_to_i))

        # If both are met, exactly one of oij or oji must hold
        both_met = And(meet[i], meet[j])
        opt.add(Implies(both_met, Or(And(oij, Not(oji)), And(oji, Not(oij)))))

# Objective: maximize the number of friends met
opt.maximize(Sum([If(meet[i], 1, 0) for i in range(n)]))

# Solve
if opt.check() != sat:
    # If something went wrong, print empty itinerary
    print(json.dumps({"itinerary": []}))
else    :
    model = opt.model()

    meetings = []
    for i, f in enumerate(friends):
        if is_true(model.eval(meet[i])):
            s = model.eval(start[i]).as_long()
            e = model.eval(end[i]).as_long()
            meetings.append({
                "person": f["name"],
                "start": s,
                "end": e
            })

    # Sort by start time
    meetings.sort(key=lambda x: x["start"])

    # Format output
    itinerary = []
    for m in meetings:
        itinerary.append({
            "action": "meet",
            "person": m["person"],
            "start_time": fmt_minutes(m["start"]),
            "end_time": fmt_minutes(m["end"])
        })

    print(json.dumps({"itinerary": itinerary}))