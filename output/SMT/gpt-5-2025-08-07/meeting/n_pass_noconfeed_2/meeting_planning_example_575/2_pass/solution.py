# SOLUTION (fixed):
from z3 import *
import json

def minutes_to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Locations
locations = [
    "The Castro",
    "Presidio",
    "Sunset District",
    "Haight-Ashbury",
    "Mission District",
    "Golden Gate Park",
    "Russian Hill",
]

# Travel times (directed, in minutes)
tt = {loc: {} for loc in locations}
# Add zero self-travel to avoid KeyError for same-location transitions
for loc in locations:
    tt[loc][loc] = 0

# The Castro ->
tt["The Castro"]["Presidio"] = 20
tt["The Castro"]["Sunset District"] = 17
tt["The Castro"]["Haight-Ashbury"] = 6
tt["The Castro"]["Mission District"] = 7
tt["The Castro"]["Golden Gate Park"] = 11
tt["The Castro"]["Russian Hill"] = 18
# Presidio ->
tt["Presidio"]["The Castro"] = 21
tt["Presidio"]["Sunset District"] = 15
tt["Presidio"]["Haight-Ashbury"] = 15
tt["Presidio"]["Mission District"] = 26
tt["Presidio"]["Golden Gate Park"] = 12
tt["Presidio"]["Russian Hill"] = 14
# Sunset District ->
tt["Sunset District"]["The Castro"] = 17
tt["Sunset District"]["Presidio"] = 16
tt["Sunset District"]["Haight-Ashbury"] = 15
tt["Sunset District"]["Mission District"] = 24
tt["Sunset District"]["Golden Gate Park"] = 11
tt["Sunset District"]["Russian Hill"] = 24
# Haight-Ashbury ->
tt["Haight-Ashbury"]["The Castro"] = 6
tt["Haight-Ashbury"]["Presidio"] = 15
tt["Haight-Ashbury"]["Sunset District"] = 15
tt["Haight-Ashbury"]["Mission District"] = 11
tt["Haight-Ashbury"]["Golden Gate Park"] = 7
tt["Haight-Ashbury"]["Russian Hill"] = 17
# Mission District ->
tt["Mission District"]["The Castro"] = 7
tt["Mission District"]["Presidio"] = 25
tt["Mission District"]["Sunset District"] = 24
tt["Mission District"]["Haight-Ashbury"] = 12
tt["Mission District"]["Golden Gate Park"] = 17
tt["Mission District"]["Russian Hill"] = 15
# Golden Gate Park ->
tt["Golden Gate Park"]["The Castro"] = 13
tt["Golden Gate Park"]["Presidio"] = 11
tt["Golden Gate Park"]["Sunset District"] = 10
tt["Golden Gate Park"]["Haight-Ashbury"] = 7
tt["Golden Gate Park"]["Mission District"] = 17
tt["Golden Gate Park"]["Russian Hill"] = 19
# Russian Hill ->
tt["Russian Hill"]["The Castro"] = 21
tt["Russian Hill"]["Presidio"] = 14
tt["Russian Hill"]["Sunset District"] = 23
tt["Russian Hill"]["Haight-Ashbury"] = 17
tt["Russian Hill"]["Mission District"] = 16
tt["Russian Hill"]["Golden Gate Park"] = 21

# People and their constraints
people = [
    {"name": "Rebecca",  "location": "Presidio",         "start": 18*60+15, "end": 20*60+45, "min": 60},
    {"name": "Linda",    "location": "Sunset District",  "start": 15*60+30, "end": 19*60+45, "min": 30},
    {"name": "Elizabeth","location": "Haight-Ashbury",   "start": 17*60+15, "end": 19*60+30, "min": 105},
    {"name": "William",  "location": "Mission District", "start": 13*60+15, "end": 19*60+30, "min": 30},
    {"name": "Robert",   "location": "Golden Gate Park", "start": 14*60+15, "end": 21*60+30, "min": 45},
    {"name": "Mark",     "location": "Russian Hill",     "start": 10*60,    "end": 21*60+15, "min": 75},
]

person_index = {p["name"]: i for i, p in enumerate(people)}

SLOTS = len(people)
START_LOCATION = "The Castro"
ARRIVAL_TIME = 9*60  # 9:00

# Helper to safely get travel time (handles same-location)
def travel_time(a, b):
    # tt[a][a] is already 0 due to prefill, but keep this safe
    if a == b:
        return 0
    return tt[a][b]

# Create solver
opt = Optimize()
opt.set(priority='lex')

# Decision variables
start = [Int(f"start_{k}") for k in range(SLOTS)]
end   = [Int(f"end_{k}") for k in range(SLOTS)]
used  = [Bool(f"used_{k}") for k in range(SLOTS)]
assign = [[Bool(f"assign_{k}_{i}") for i in range(len(people))] for k in range(SLOTS)]

# Bounds and basic relations
for k in range(SLOTS):
    opt.add(start[k] >= 0, start[k] <= 24*60)
    opt.add(end[k] >= 0, end[k] <= 24*60)
    # each slot assigned to at most one person
    opt.add(AtMost(*assign[k], 1))
    # used iff assigned to someone
    opt.add(used[k] == Or(*assign[k]))
    # if not used, zero time
    opt.add(Implies(Not(used[k]), And(start[k] == 0, end[k] == 0)))

# Each person is met at most once
for i in range(len(people)):
    opt.add(AtMost(*[assign[k][i] for k in range(SLOTS)], 1))

# Contiguity: no gaps (used[k+1] -> used[k])
for k in range(1, SLOTS):
    opt.add(Implies(used[k], used[k-1]))

# Meeting window and minimum duration per assignment
for k in range(SLOTS):
    for i, p in enumerate(people):
        s_avail = p["start"]
        e_avail = p["end"]
        min_dur = p["min"]
        opt.add(Implies(assign[k][i], And(
            start[k] >= s_avail,
            end[k] <= e_avail,
            end[k] - start[k] >= min_dur
        )))

# Travel constraints between consecutive used slots
for k in range(SLOTS - 1):
    for i, p_i in enumerate(people):
        for j, p_j in enumerate(people):
            loc_i = p_i["location"]
            loc_j = p_j["location"]
            travel_ij = travel_time(loc_i, loc_j)
            opt.add(Implies(And(assign[k][i], assign[k+1][j]),
                            start[k+1] >= end[k] + travel_ij))

# Travel from start location to first used slot
for i, p in enumerate(people):
    travel0 = travel_time(START_LOCATION, p["location"])
    opt.add(Implies(assign[0][i], start[0] >= ARRIVAL_TIME + travel0))

# Day end to optionally minimize
day_end = Int("day_end")
opt.add(day_end >= 0, day_end <= 24*60)
for k in range(SLOTS):
    opt.add(day_end >= end[k])

# Objective 1: maximize number of people met
person_met = [Bool(f"met_{i}") for i in range(len(people))]
for i in range(len(people)):
    opt.add(person_met[i] == Or(*[assign[k][i] for k in range(SLOTS)]))
opt.maximize(Sum([If(person_met[i], 1, 0) for i in range(len(people))]))

# Objective 2: maximize total meeting time
total_meeting_time = Sum([If(used[k], end[k] - start[k], 0) for k in range(SLOTS)])
opt.maximize(total_meeting_time)

# Objective 3: minimize finishing time
opt.minimize(day_end)

# Solve
if opt.check() != sat:
    # Fallback empty itinerary if unsat (should not happen)
    result = {"itinerary": []}
    print(json.dumps(result))
    raise SystemExit()

m = opt.model()

# Build itinerary
itinerary = []
for k in range(SLOTS):
    if is_true(m.evaluate(used[k], model_completion=True)):
        # Find assigned person
        assigned_person_idx = None
        for i in range(len(people)):
            if is_true(m.evaluate(assign[k][i], model_completion=True)):
                assigned_person_idx = i
                break
        if assigned_person_idx is None:
            continue
        p = people[assigned_person_idx]
        st = m.evaluate(start[k]).as_long()
        en = m.evaluate(end[k]).as_long()
        itinerary.append({
            "action": "meet",
            "location": p["location"],
            "person": p["name"],
            "start_time": minutes_to_str(st),
            "end_time": minutes_to_str(en)
        })

# Output JSON
print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))