import json
from z3 import Optimize, Int, Bool, If, And, Or, Sum, is_true, sat

# Time helper
def t(h, m):
    return h * 60 + m

def fmt_time(mins):
    h = mins // 60
    m = mins % 60
    return f"{h}:{m:02d}"

# Locations
locations = [
    "Russian Hill",
    "Marina District",
    "Financial District",
    "Alamo Square",
    "Golden Gate Park",
    "The Castro",
    "Bayview",
    "Sunset District",
    "Haight-Ashbury",
    "Nob Hill",
]

# Travel times (minutes), directed
travel = {
    "Russian Hill": {
        "Marina District": 7,
        "Financial District": 11,
        "Alamo Square": 15,
        "Golden Gate Park": 21,
        "The Castro": 21,
        "Bayview": 23,
        "Sunset District": 23,
        "Haight-Ashbury": 17,
        "Nob Hill": 5,
    },
    "Marina District": {
        "Russian Hill": 8,
        "Financial District": 17,
        "Alamo Square": 15,
        "Golden Gate Park": 18,
        "The Castro": 22,
        "Bayview": 27,
        "Sunset District": 19,
        "Haight-Ashbury": 16,
        "Nob Hill": 12,
    },
    "Financial District": {
        "Russian Hill": 11,
        "Marina District": 15,
        "Alamo Square": 17,
        "Golden Gate Park": 23,
        "The Castro": 20,
        "Bayview": 19,
        "Sunset District": 30,
        "Haight-Ashbury": 19,
        "Nob Hill": 8,
    },
    "Alamo Square": {
        "Russian Hill": 13,
        "Marina District": 15,
        "Financial District": 17,
        "Golden Gate Park": 9,
        "The Castro": 8,
        "Bayview": 16,
        "Sunset District": 16,
        "Haight-Ashbury": 5,
        "Nob Hill": 11,
    },
    "Golden Gate Park": {
        "Russian Hill": 19,
        "Marina District": 16,
        "Financial District": 26,
        "Alamo Square": 9,
        "The Castro": 13,
        "Bayview": 23,
        "Sunset District": 10,
        "Haight-Ashbury": 7,
        "Nob Hill": 20,
    },
    "The Castro": {
        "Russian Hill": 18,
        "Marina District": 21,
        "Financial District": 21,
        "Alamo Square": 8,
        "Golden Gate Park": 11,
        "Bayview": 19,
        "Sunset District": 17,
        "Haight-Ashbury": 6,
        "Nob Hill": 16,
    },
    "Bayview": {
        "Russian Hill": 23,
        "Marina District": 27,
        "Financial District": 19,
        "Alamo Square": 16,
        "Golden Gate Park": 22,
        "The Castro": 19,
        "Sunset District": 23,
        "Haight-Ashbury": 19,
        "Nob Hill": 20,
    },
    "Sunset District": {
        "Russian Hill": 24,
        "Marina District": 21,
        "Financial District": 30,
        "Alamo Square": 17,
        "Golden Gate Park": 11,
        "The Castro": 17,
        "Bayview": 22,
        "Haight-Ashbury": 15,
        "Nob Hill": 27,
    },
    "Haight-Ashbury": {
        "Russian Hill": 17,
        "Marina District": 17,
        "Financial District": 21,
        "Alamo Square": 5,
        "Golden Gate Park": 7,
        "The Castro": 6,
        "Bayview": 18,
        "Sunset District": 15,
        "Nob Hill": 15,
    },
    "Nob Hill": {
        "Russian Hill": 5,
        "Marina District": 11,
        "Financial District": 9,
        "Alamo Square": 11,
        "Golden Gate Park": 17,
        "The Castro": 17,
        "Bayview": 19,
        "Sunset District": 24,
        "Haight-Ashbury": 13,
    },
}

# Add self-travel zero entries and fill missing entries with a large number
for a in locations:
    travel.setdefault(a, {})
    for b in locations:
        if a == b:
            travel[a][b] = 0
        else:
            if b not in travel[a]:
                travel[a][b] = 9999

# Friends and their constraints
friends = {
    "Mark": {
        "location": "Marina District",
        "avail_start": t(18, 45),
        "avail_end": t(21, 0),
        "min_duration": 90,
    },
    "Karen": {
        "location": "Financial District",
        "avail_start": t(9, 30),
        "avail_end": t(12, 45),
        "min_duration": 90,
    },
    "Barbara": {
        "location": "Alamo Square",
        "avail_start": t(10, 0),
        "avail_end": t(19, 30),
        "min_duration": 90,
    },
    "Nancy": {
        "location": "Golden Gate Park",
        "avail_start": t(16, 45),
        "avail_end": t(20, 0),
        "min_duration": 105,
    },
    "David": {
        "location": "The Castro",
        "avail_start": t(9, 0),
        "avail_end": t(18, 0),
        "min_duration": 120,
    },
    "Linda": {
        "location": "Bayview",
        "avail_start": t(18, 15),
        "avail_end": t(19, 45),
        "min_duration": 45,
    },
    "Kevin": {
        "location": "Sunset District",
        "avail_start": t(10, 0),
        "avail_end": t(17, 45),
        "min_duration": 120,
    },
    "Matthew": {
        "location": "Haight-Ashbury",
        "avail_start": t(10, 15),
        "avail_end": t(15, 30),
        "min_duration": 45,
    },
    "Andrew": {
        "location": "Nob Hill",
        "avail_start": t(11, 45),
        "avail_end": t(16, 45),
        "min_duration": 105,
    },
}

# Day start and start location
day_start_time = t(9, 0)
start_location = "Russian Hill"

# Create Optimize solver
opt = Optimize()
opt.set(priority='lex')

# Variables
s_vars = {}
e_vars = {}
meet_vars = {}
for name in friends:
    s_vars[name] = Int(f"s_{name}")
    e_vars[name] = Int(f"e_{name}")
    meet_vars[name] = Bool(f"meet_{name}")

    fs = friends[name]["avail_start"]
    fe = friends[name]["avail_end"]
    md = friends[name]["min_duration"]
    loc = friends[name]["location"]

    # Domain and linkage constraints
    opt.add(s_vars[name] >= 0, e_vars[name] >= 0, e_vars[name] >= s_vars[name])

    # If meeting, enforce availability and minimum duration; else zero them to avoid interference
    opt.add(If(
        meet_vars[name],
        And(s_vars[name] >= fs, e_vars[name] <= fe, e_vars[name] - s_vars[name] >= md),
        And(s_vars[name] == 0, e_vars[name] == 0)
    ))

    # Travel time constraint from start location to this friend's start time if meeting
    opt.add(If(meet_vars[name], s_vars[name] >= day_start_time + travel[start_location][loc], True))

# Pairwise non-overlap with travel times
names = list(friends.keys())
for i in range(len(names)):
    for j in range(i + 1, len(names)):
        ni = names[i]
        nj = names[j]
        li = friends[ni]["location"]
        lj = friends[nj]["location"]
        tij = travel[li][lj]
        tji = travel[lj][li]
        opt.add(
            If(
                And(meet_vars[ni], meet_vars[nj]),
                Or(e_vars[ni] + tij <= s_vars[nj], e_vars[nj] + tji <= s_vars[ni]),
                True
            )
        )

# Objective 1: maximize number of friends met
count_meet = Sum([If(meet_vars[name], 1, 0) for name in names])
opt.maximize(count_meet)

# Objective 2: maximize total meeting minutes
total_minutes = Sum([If(meet_vars[name], e_vars[name] - s_vars[name], 0) for name in names])
opt.maximize(total_minutes)

# Solve
res = opt.check()
if res == sat:
    model = opt.model()
    itinerary = []
    for name in names:
        if is_true(model.evaluate(meet_vars[name])):
            s = model.evaluate(s_vars[name]).as_long()
            e = model.evaluate(e_vars[name]).as_long()
            itinerary.append({
                "action": "meet",
                "location": friends[name]["location"],
                "person": name,
                "start_time": fmt_time(s),
                "end_time": fmt_time(e),
                "start_min": s  # for sorting
            })
    itinerary.sort(key=lambda x: x["start_min"])
    for item in itinerary:
        del item["start_min"]
    output = {"itinerary": itinerary}
else:
    output = {"itinerary": []}

print(json.dumps(output, ensure_ascii=False, indent=2))