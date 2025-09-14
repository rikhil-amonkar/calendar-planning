import json
from z3 import *

def t(h, m):
    return h * 60 + m

def minutes_to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Locations
locations = [
    "Richmond District", "The Castro", "Nob Hill", "Marina District", "Pacific Heights",
    "Haight-Ashbury", "Mission District", "Chinatown", "Russian Hill", "Alamo Square", "Bayview"
]

# Travel times (minutes)
travel = {loc: {} for loc in locations}
def set_travel(a, b, minutes):
    travel[a][b] = minutes

# Populate travel times
set_travel("Richmond District", "The Castro", 16)
set_travel("Richmond District", "Nob Hill", 17)
set_travel("Richmond District", "Marina District", 9)
set_travel("Richmond District", "Pacific Heights", 10)
set_travel("Richmond District", "Haight-Ashbury", 10)
set_travel("Richmond District", "Mission District", 20)
set_travel("Richmond District", "Chinatown", 20)
set_travel("Richmond District", "Russian Hill", 13)
set_travel("Richmond District", "Alamo Square", 13)
set_travel("Richmond District", "Bayview", 27)

set_travel("The Castro", "Richmond District", 16)
set_travel("The Castro", "Nob Hill", 16)
set_travel("The Castro", "Marina District", 21)
set_travel("The Castro", "Pacific Heights", 16)
set_travel("The Castro", "Haight-Ashbury", 6)
set_travel("The Castro", "Mission District", 7)
set_travel("The Castro", "Chinatown", 22)
set_travel("The Castro", "Russian Hill", 18)
set_travel("The Castro", "Alamo Square", 8)
set_travel("The Castro", "Bayview", 19)

set_travel("Nob Hill", "Richmond District", 14)
set_travel("Nob Hill", "The Castro", 17)
set_travel("Nob Hill", "Marina District", 11)
set_travel("Nob Hill", "Pacific Heights", 8)
set_travel("Nob Hill", "Haight-Ashbury", 13)
set_travel("Nob Hill", "Mission District", 13)
set_travel("Nob Hill", "Chinatown", 6)
set_travel("Nob Hill", "Russian Hill", 5)
set_travel("Nob Hill", "Alamo Square", 11)
set_travel("Nob Hill", "Bayview", 19)

set_travel("Marina District", "Richmond District", 11)
set_travel("Marina District", "The Castro", 22)
set_travel("Marina District", "Nob Hill", 12)
set_travel("Marina District", "Pacific Heights", 7)
set_travel("Marina District", "Haight-Ashbury", 16)
set_travel("Marina District", "Mission District", 20)
set_travel("Marina District", "Chinatown", 15)
set_travel("Marina District", "Russian Hill", 8)
set_travel("Marina District", "Alamo Square", 15)
set_travel("Marina District", "Bayview", 27)

set_travel("Pacific Heights", "Richmond District", 12)
set_travel("Pacific Heights", "The Castro", 16)
set_travel("Pacific Heights", "Nob Hill", 8)
set_travel("Pacific Heights", "Marina District", 6)
set_travel("Pacific Heights", "Haight-Ashbury", 11)
set_travel("Pacific Heights", "Mission District", 15)
set_travel("Pacific Heights", "Chinatown", 11)
set_travel("Pacific Heights", "Russian Hill", 7)
set_travel("Pacific Heights", "Alamo Square", 10)
set_travel("Pacific Heights", "Bayview", 22)

set_travel("Haight-Ashbury", "Richmond District", 10)
set_travel("Haight-Ashbury", "The Castro", 6)
set_travel("Haight-Ashbury", "Nob Hill", 15)
set_travel("Haight-Ashbury", "Marina District", 17)
set_travel("Haight-Ashbury", "Pacific Heights", 12)
set_travel("Haight-Ashbury", "Mission District", 11)
set_travel("Haight-Ashbury", "Chinatown", 19)
set_travel("Haight-Ashbury", "Russian Hill", 17)
set_travel("Haight-Ashbury", "Alamo Square", 5)
set_travel("Haight-Ashbury", "Bayview", 18)

set_travel("Mission District", "Richmond District", 20)
set_travel("Mission District", "The Castro", 7)
set_travel("Mission District", "Nob Hill", 12)
set_travel("Mission District", "Marina District", 19)
set_travel("Mission District", "Pacific Heights", 16)
set_travel("Mission District", "Haight-Ashbury", 12)
set_travel("Mission District", "Chinatown", 16)
set_travel("Mission District", "Russian Hill", 15)
set_travel("Mission District", "Alamo Square", 11)
set_travel("Mission District", "Bayview", 14)

set_travel("Chinatown", "Richmond District", 20)
set_travel("Chinatown", "The Castro", 22)
set_travel("Chinatown", "Nob Hill", 9)
set_travel("Chinatown", "Marina District", 12)
set_travel("Chinatown", "Pacific Heights", 10)
set_travel("Chinatown", "Haight-Ashbury", 19)
set_travel("Chinatown", "Mission District", 17)
set_travel("Chinatown", "Russian Hill", 7)
set_travel("Chinatown", "Alamo Square", 17)
set_travel("Chinatown", "Bayview", 20)

set_travel("Russian Hill", "Richmond District", 14)
set_travel("Russian Hill", "The Castro", 21)
set_travel("Russian Hill", "Nob Hill", 5)
set_travel("Russian Hill", "Marina District", 7)
set_travel("Russian Hill", "Pacific Heights", 7)
set_travel("Russian Hill", "Haight-Ashbury", 17)
set_travel("Russian Hill", "Mission District", 16)
set_travel("Russian Hill", "Chinatown", 9)
set_travel("Russian Hill", "Alamo Square", 15)
set_travel("Russian Hill", "Bayview", 23)

set_travel("Alamo Square", "Richmond District", 11)
set_travel("Alamo Square", "The Castro", 8)
set_travel("Alamo Square", "Nob Hill", 11)
set_travel("Alamo Square", "Marina District", 15)
set_travel("Alamo Square", "Pacific Heights", 10)
set_travel("Alamo Square", "Haight-Ashbury", 5)
set_travel("Alamo Square", "Mission District", 10)
set_travel("Alamo Square", "Chinatown", 15)
set_travel("Alamo Square", "Russian Hill", 13)
set_travel("Alamo Square", "Bayview", 16)

set_travel("Bayview", "Richmond District", 25)
set_travel("Bayview", "The Castro", 19)
set_travel("Bayview", "Nob Hill", 20)
set_travel("Bayview", "Marina District", 27)
set_travel("Bayview", "Pacific Heights", 23)
set_travel("Bayview", "Haight-Ashbury", 19)
set_travel("Bayview", "Mission District", 13)
set_travel("Bayview", "Chinatown", 19)
set_travel("Bayview", "Russian Hill", 23)
set_travel("Bayview", "Alamo Square", 16)

# Ensure travel within same location is zero
for a in locations:
    travel[a][a] = 0

def travel_time(a, b):
    return travel[a][b]

# People data: name, location, availability start/end, minimum duration
people = [
    {"name": "Matthew", "loc": "The Castro", "start": t(16,30), "end": t(20,0), "min_dur": 45},
    {"name": "Rebecca", "loc": "Nob Hill", "start": t(15,15), "end": t(19,15), "min_dur": 105},
    {"name": "Brian", "loc": "Marina District", "start": t(14,15), "end": t(22,0), "min_dur": 30},
    {"name": "Emily", "loc": "Pacific Heights", "start": t(11,15), "end": t(19,45), "min_dur": 15},
    {"name": "Karen", "loc": "Haight-Ashbury", "start": t(11,45), "end": t(17,30), "min_dur": 30},
    {"name": "Stephanie", "loc": "Mission District", "start": t(13,0), "end": t(15,45), "min_dur": 75},
    {"name": "James", "loc": "Chinatown", "start": t(14,30), "end": t(19,0), "min_dur": 120},
    {"name": "Steven", "loc": "Russian Hill", "start": t(14,0), "end": t(20,0), "min_dur": 30},
    {"name": "Elizabeth", "loc": "Alamo Square", "start": t(13,0), "end": t(17,15), "min_dur": 120},
    {"name": "William", "loc": "Bayview", "start": t(18,15), "end": t(20,15), "min_dur": 90},
]

# Start location/time
start_location = "Richmond District"
arrival_time = t(9, 0)

# Z3 variables
opt = Optimize()
opt.set(priority='lex')

s_vars = {}
e_vars = {}
meet_vars = {}

for p in people:
    var_base = p["name"].replace(" ", "_")
    s = Int(f"{var_base}_start")
    e = Int(f"{var_base}_end")
    meet = Bool(f"{var_base}_meet")
    s_vars[p["name"]] = s
    e_vars[p["name"]] = e
    meet_vars[p["name"]] = meet

    # Bounds
    opt.add(s >= 0, s <= 24*60, e >= 0, e <= 24*60)

    # If meeting, times within availability; else zeroed
    opt.add(If(meet, s >= p["start"], s == 0))
    opt.add(If(meet, e <= p["end"], e == 0))
    opt.add(If(meet, e - s >= p["min_dur"], e == s))

    # Must be reachable from start location at 9:00
    opt.add(Or(Not(meet), arrival_time + travel_time(start_location, p["loc"]) <= s))

# Non-overlap with travel between all meetings
n = len(people)
for i in range(n):
    for j in range(i+1, n):
        pi = people[i]
        pj = people[j]
        si, ei, mi = s_vars[pi["name"]], e_vars[pi["name"]], meet_vars[pi["name"]]
        sj, ej, mj = s_vars[pj["name"]], e_vars[pj["name"]], meet_vars[pj["name"]]
        ti_to_j = travel_time(pi["loc"], pj["loc"])
        tj_to_i = travel_time(pj["loc"], pi["loc"])
        # If both meetings happen, enforce disjunctive ordering with travel
        opt.add(Or(Not(And(mi, mj)),
                   ei + ti_to_j <= sj,
                   ej + tj_to_i <= si))

# Objective: maximize number of meetings, then maximize total meeting time
total_meets = Sum([If(meet_vars[p["name"]], 1, 0) for p in people])
total_minutes = Sum([If(meet_vars[p["name"]], e_vars[p["name"]] - s_vars[p["name"]], 0) for p in people])
opt.maximize(total_meets)
opt.maximize(total_minutes)

if opt.check() != sat:
    print(json.dumps({"itinerary": []}))
else:
    m = opt.model()
    itinerary = []
    for p in people:
        if is_true(m.evaluate(meet_vars[p["name"]])):
            s_val = m.evaluate(s_vars[p["name"]]).as_long()
            e_val = m.evaluate(e_vars[p["name"]]).as_long()
            itinerary.append({
                "action": "meet",
                "location": p["loc"],
                "person": p["name"],
                "start_time": minutes_to_str(s_val),
                "end_time": minutes_to_str(e_val)
            })
    # Sort by start_time
    itinerary.sort(key=lambda x: int(x["start_time"].split(":")[0]) * 60 + int(x["start_time"].split(":")[1]))
    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))