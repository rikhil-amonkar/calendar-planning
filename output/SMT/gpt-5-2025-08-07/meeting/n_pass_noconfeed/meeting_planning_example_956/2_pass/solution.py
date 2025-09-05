import json
from z3 import *

def minutes(h, m):
    return h * 60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Locations
locations = [
    "The Castro",
    "Alamo Square",
    "Richmond District",
    "Financial District",
    "Union Square",
    "Fisherman's Wharf",
    "Marina District",
    "Haight-Ashbury",
    "Mission District",
    "Pacific Heights",
    "Golden Gate Park",
]

# Travel times (minutes)
T = {loc: {} for loc in locations}
def set_t(a, b, t):
    T[a][b] = t

# The Castro
set_t("The Castro", "Alamo Square", 8)
set_t("The Castro", "Richmond District", 16)
set_t("The Castro", "Financial District", 21)
set_t("The Castro", "Union Square", 19)
set_t("The Castro", "Fisherman's Wharf", 24)
set_t("The Castro", "Marina District", 21)
set_t("The Castro", "Haight-Ashbury", 6)
set_t("The Castro", "Mission District", 7)
set_t("The Castro", "Pacific Heights", 16)
set_t("The Castro", "Golden Gate Park", 11)

# Alamo Square
set_t("Alamo Square", "The Castro", 8)
set_t("Alamo Square", "Richmond District", 11)
set_t("Alamo Square", "Financial District", 17)
set_t("Alamo Square", "Union Square", 14)
set_t("Alamo Square", "Fisherman's Wharf", 19)
set_t("Alamo Square", "Marina District", 15)
set_t("Alamo Square", "Haight-Ashbury", 5)
set_t("Alamo Square", "Mission District", 10)
set_t("Alamo Square", "Pacific Heights", 10)
set_t("Alamo Square", "Golden Gate Park", 9)

# Richmond District
set_t("Richmond District", "The Castro", 16)
set_t("Richmond District", "Alamo Square", 13)
set_t("Richmond District", "Financial District", 22)
set_t("Richmond District", "Union Square", 21)
set_t("Richmond District", "Fisherman's Wharf", 18)
set_t("Richmond District", "Marina District", 9)
set_t("Richmond District", "Haight-Ashbury", 10)
set_t("Richmond District", "Mission District", 20)
set_t("Richmond District", "Pacific Heights", 10)
set_t("Richmond District", "Golden Gate Park", 9)

# Financial District
set_t("Financial District", "The Castro", 20)
set_t("Financial District", "Alamo Square", 17)
set_t("Financial District", "Richmond District", 21)
set_t("Financial District", "Union Square", 9)
set_t("Financial District", "Fisherman's Wharf", 10)
set_t("Financial District", "Marina District", 15)
set_t("Financial District", "Haight-Ashbury", 19)
set_t("Financial District", "Mission District", 17)
set_t("Financial District", "Pacific Heights", 13)
set_t("Financial District", "Golden Gate Park", 23)

# Union Square
set_t("Union Square", "The Castro", 17)
set_t("Union Square", "Alamo Square", 15)
set_t("Union Square", "Richmond District", 20)
set_t("Union Square", "Financial District", 9)
set_t("Union Square", "Fisherman's Wharf", 15)
set_t("Union Square", "Marina District", 18)
set_t("Union Square", "Haight-Ashbury", 18)
set_t("Union Square", "Mission District", 14)
set_t("Union Square", "Pacific Heights", 15)
set_t("Union Square", "Golden Gate Park", 22)

# Fisherman's Wharf
set_t("Fisherman's Wharf", "The Castro", 27)
set_t("Fisherman's Wharf", "Alamo Square", 21)
set_t("Fisherman's Wharf", "Richmond District", 18)
set_t("Fisherman's Wharf", "Financial District", 11)
set_t("Fisherman's Wharf", "Union Square", 13)
set_t("Fisherman's Wharf", "Marina District", 9)
set_t("Fisherman's Wharf", "Haight-Ashbury", 22)
set_t("Fisherman's Wharf", "Mission District", 22)
set_t("Fisherman's Wharf", "Pacific Heights", 12)
set_t("Fisherman's Wharf", "Golden Gate Park", 25)

# Marina District
set_t("Marina District", "The Castro", 22)
set_t("Marina District", "Alamo Square", 15)
set_t("Marina District", "Richmond District", 11)
set_t("Marina District", "Financial District", 17)
set_t("Marina District", "Union Square", 16)
set_t("Marina District", "Fisherman's Wharf", 10)
set_t("Marina District", "Haight-Ashbury", 16)
set_t("Marina District", "Mission District", 20)
set_t("Marina District", "Pacific Heights", 7)
set_t("Marina District", "Golden Gate Park", 18)

# Haight-Ashbury
set_t("Haight-Ashbury", "The Castro", 6)
set_t("Haight-Ashbury", "Alamo Square", 5)
set_t("Haight-Ashbury", "Richmond District", 10)
set_t("Haight-Ashbury", "Financial District", 21)
set_t("Haight-Ashbury", "Union Square", 19)
set_t("Haight-Ashbury", "Fisherman's Wharf", 23)
set_t("Haight-Ashbury", "Marina District", 17)
set_t("Haight-Ashbury", "Mission District", 11)
set_t("Haight-Ashbury", "Pacific Heights", 12)
set_t("Haight-Ashbury", "Golden Gate Park", 7)

# Mission District
set_t("Mission District", "The Castro", 7)
set_t("Mission District", "Alamo Square", 11)
set_t("Mission District", "Richmond District", 20)
set_t("Mission District", "Financial District", 15)
set_t("Mission District", "Union Square", 15)
set_t("Mission District", "Fisherman's Wharf", 22)
set_t("Mission District", "Marina District", 19)
set_t("Mission District", "Haight-Ashbury", 12)
set_t("Mission District", "Pacific Heights", 16)
set_t("Mission District", "Golden Gate Park", 17)

# Pacific Heights
set_t("Pacific Heights", "The Castro", 16)
set_t("Pacific Heights", "Alamo Square", 10)
set_t("Pacific Heights", "Richmond District", 12)
set_t("Pacific Heights", "Financial District", 13)
set_t("Pacific Heights", "Union Square", 12)
set_t("Pacific Heights", "Fisherman's Wharf", 13)
set_t("Pacific Heights", "Marina District", 6)
set_t("Pacific Heights", "Haight-Ashbury", 11)
set_t("Pacific Heights", "Mission District", 15)
set_t("Pacific Heights", "Golden Gate Park", 15)

# Golden Gate Park
set_t("Golden Gate Park", "The Castro", 13)
set_t("Golden Gate Park", "Alamo Square", 9)
set_t("Golden Gate Park", "Richmond District", 7)
set_t("Golden Gate Park", "Financial District", 26)
set_t("Golden Gate Park", "Union Square", 22)
set_t("Golden Gate Park", "Fisherman's Wharf", 24)
set_t("Golden Gate Park", "Marina District", 16)
set_t("Golden Gate Park", "Haight-Ashbury", 7)
set_t("Golden Gate Park", "Mission District", 17)
set_t("Golden Gate Park", "Pacific Heights", 16)

# Ensure zero travel time for same-origin/destination to prevent KeyError
for loc in locations:
    T[loc][loc] = 0

# People and their constraints
people = [
    {"name": "William",  "location": "Alamo Square",        "start": minutes(15, 15), "end": minutes(17, 15), "min_dur": 60},
    {"name": "Joshua",   "location": "Richmond District",    "start": minutes(7, 0),   "end": minutes(20, 0),  "min_dur": 15},
    {"name": "Joseph",   "location": "Financial District",   "start": minutes(11,15),  "end": minutes(13,30),  "min_dur": 15},
    {"name": "David",    "location": "Union Square",         "start": minutes(16,45),  "end": minutes(19,15),  "min_dur": 45},
    {"name": "Brian",    "location": "Fisherman's Wharf",    "start": minutes(13,45),  "end": minutes(20,45),  "min_dur": 105},
    {"name": "Karen",    "location": "Marina District",      "start": minutes(11,30),  "end": minutes(18,30),  "min_dur": 15},
    {"name": "Anthony",  "location": "Haight-Ashbury",       "start": minutes(7,15),   "end": minutes(10,30),  "min_dur": 30},
    {"name": "Matthew",  "location": "Mission District",     "start": minutes(17,15),  "end": minutes(19,15),  "min_dur": 120},
    {"name": "Helen",    "location": "Pacific Heights",      "start": minutes(8,0),    "end": minutes(12,0),   "min_dur": 75},
    {"name": "Jeffrey",  "location": "Golden Gate Park",     "start": minutes(19,0),   "end": minutes(21,30),  "min_dur": 60},
]
N = len(people)
K = N  # number of slots

# Map person index to location
person_locations = [p["location"] for p in people]

# SMT variables
opt = Optimize()
opt.set(priority='lex')

person_vars = [Int(f"person_{s}") for s in range(K)]
start_vars = [Int(f"start_{s}") for s in range(K)]
end_vars = [Int(f"end_{s}") for s in range(K)]

# Domain constraints
for s in range(K):
    # person index: -1 means empty; else 0..N-1
    opt.add(Or(person_vars[s] == -1, And(person_vars[s] >= 0, person_vars[s] < N)))
    # time bounds within a day
    opt.add(And(start_vars[s] >= 0, start_vars[s] <= 24*60 - 1))
    opt.add(And(end_vars[s] >= 0, end_vars[s] <= 24*60 - 1))
    # if empty slot, zero duration
    opt.add(Implies(person_vars[s] == -1, end_vars[s] == start_vars[s]))

# Pack non-empty slots to the front (no gaps)
for s in range(K - 1):
    opt.add(Implies(person_vars[s] == -1, person_vars[s + 1] == -1))

# Each person used at most once
for p in range(N):
    opt.add(Sum([If(person_vars[s] == p, 1, 0) for s in range(K)]) <= 1)

# Meeting-specific constraints per slot
for s in range(K):
    for p in range(N):
        p_info = people[p]
        loc = p_info["location"]
        avail_start = p_info["start"]
        avail_end = p_info["end"]
        min_dur = p_info["min_dur"]
        # If slot s is assigned to person p, enforce availability and duration
        opt.add(Implies(person_vars[s] == p, And(
            start_vars[s] >= avail_start,
            end_vars[s] <= avail_end,
            end_vars[s] > start_vars[s],
            end_vars[s] - start_vars[s] >= min_dur
        )))
    # Additional: if slot s is assigned, start after earliest possible arrival from The Castro for slot 0
    if s == 0:
        conds = []
        for p in range(N):
            loc = people[p]["location"]
            # Safe lookup: 0 if already at The Castro, else matrix value
            travel_time = 0 if loc == "The Castro" else T["The Castro"][loc]
            conds.append(Implies(person_vars[s] == p, start_vars[s] >= minutes(9,0) + travel_time))
        opt.add(And(conds))

# Travel constraints between consecutive non-empty slots
for s in range(K - 1):
    for p1 in range(N):
        for p2 in range(N):
            loc1 = people[p1]["location"]
            loc2 = people[p2]["location"]
            # Safe lookup with same-location = 0
            travel_time = 0 if loc1 == loc2 else T[loc1][loc2]
            opt.add(Implies(And(person_vars[s] == p1, person_vars[s + 1] == p2),
                            start_vars[s + 1] >= end_vars[s] + travel_time))

# Objective: maximize number of meetings, then maximize total minutes
used_slots = [If(person_vars[s] != -1, 1, 0) for s in range(K)]
total_meetings = Sum(used_slots)
total_minutes = Sum([If(person_vars[s] != -1, end_vars[s] - start_vars[s], 0) for s in range(K)])
opt.maximize(total_meetings)
opt.maximize(total_minutes)

# Solve
if opt.check() == sat:
    model = opt.model()
    itinerary = []
    for s in range(K):
        pv = model.evaluate(person_vars[s]).as_long()
        if pv == -1:
            break
        start_m = model.evaluate(start_vars[s]).as_long()
        end_m = model.evaluate(end_vars[s]).as_long()
        person = people[pv]["name"]
        location = people[pv]["location"]
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": fmt_time(start_m),
            "end_time": fmt_time(end_m)
        })
    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))
else:
    print(json.dumps({"itinerary": []}, ensure_ascii=False))