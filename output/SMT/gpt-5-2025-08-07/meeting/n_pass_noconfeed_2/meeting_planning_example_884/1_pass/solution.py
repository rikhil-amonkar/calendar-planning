import json
from z3 import *

def time_to_min(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def min_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Locations
locations = [
    "Richmond District",
    "Chinatown",
    "Sunset District",
    "Alamo Square",
    "Financial District",
    "North Beach",
    "Embarcadero",
    "Presidio",
    "Golden Gate Park",
    "Bayview",
]

# Travel times in minutes (directed)
travel = {
    "Richmond District": {
        "Chinatown": 20,
        "Sunset District": 11,
        "Alamo Square": 13,
        "Financial District": 22,
        "North Beach": 17,
        "Embarcadero": 19,
        "Presidio": 7,
        "Golden Gate Park": 9,
        "Bayview": 27,
    },
    "Chinatown": {
        "Richmond District": 20,
        "Sunset District": 29,
        "Alamo Square": 17,
        "Financial District": 5,
        "North Beach": 3,
        "Embarcadero": 5,
        "Presidio": 19,
        "Golden Gate Park": 23,
        "Bayview": 20,
    },
    "Sunset District": {
        "Richmond District": 12,
        "Chinatown": 30,
        "Alamo Square": 17,
        "Financial District": 30,
        "North Beach": 28,
        "Embarcadero": 30,
        "Presidio": 16,
        "Golden Gate Park": 11,
        "Bayview": 22,
    },
    "Alamo Square": {
        "Richmond District": 11,
        "Chinatown": 15,
        "Sunset District": 16,
        "Financial District": 17,
        "North Beach": 15,
        "Embarcadero": 16,
        "Presidio": 17,
        "Golden Gate Park": 9,
        "Bayview": 16,
    },
    "Financial District": {
        "Richmond District": 21,
        "Chinatown": 5,
        "Sunset District": 30,
        "Alamo Square": 17,
        "North Beach": 7,
        "Embarcadero": 4,
        "Presidio": 22,
        "Golden Gate Park": 23,
        "Bayview": 19,
    },
    "North Beach": {
        "Richmond District": 18,
        "Chinatown": 6,
        "Sunset District": 27,
        "Alamo Square": 16,
        "Financial District": 8,
        "Embarcadero": 6,
        "Presidio": 17,
        "Golden Gate Park": 22,
        "Bayview": 25,
    },
    "Embarcadero": {
        "Richmond District": 21,
        "Chinatown": 7,
        "Sunset District": 30,
        "Alamo Square": 19,
        "Financial District": 5,
        "North Beach": 5,
        "Presidio": 20,
        "Golden Gate Park": 25,
        "Bayview": 21,
    },
    "Presidio": {
        "Richmond District": 7,
        "Chinatown": 21,
        "Sunset District": 15,
        "Alamo Square": 19,
        "Financial District": 23,
        "North Beach": 18,
        "Embarcadero": 20,
        "Golden Gate Park": 12,
        "Bayview": 31,
    },
    "Golden Gate Park": {
        "Richmond District": 7,
        "Chinatown": 23,
        "Sunset District": 10,
        "Alamo Square": 9,
        "Financial District": 26,
        "North Beach": 23,
        "Embarcadero": 25,
        "Presidio": 11,
        "Bayview": 23,
    },
    "Bayview": {
        "Richmond District": 25,
        "Chinatown": 19,
        "Sunset District": 23,
        "Alamo Square": 16,
        "Financial District": 19,
        "North Beach": 22,
        "Embarcadero": 19,
        "Presidio": 32,
        "Golden Gate Park": 22,
    },
}

# Friends and constraints
friends = [
    {
        "name": "Robert",
        "location": "Chinatown",
        "avail_start": "7:45",
        "avail_end": "17:30",
        "min_duration": 120,
    },
    {
        "name": "David",
        "location": "Sunset District",
        "avail_start": "12:30",
        "avail_end": "19:45",
        "min_duration": 45,
    },
    {
        "name": "Matthew",
        "location": "Alamo Square",
        "avail_start": "8:45",
        "avail_end": "13:45",
        "min_duration": 90,
    },
    {
        "name": "Jessica",
        "location": "Financial District",
        "avail_start": "9:30",
        "avail_end": "18:45",
        "min_duration": 45,
    },
    {
        "name": "Melissa",
        "location": "North Beach",
        "avail_start": "7:15",
        "avail_end": "16:45",
        "min_duration": 45,
    },
    {
        "name": "Mark",
        "location": "Embarcadero",
        "avail_start": "15:15",
        "avail_end": "17:00",
        "min_duration": 45,
    },
    {
        "name": "Deborah",
        "location": "Presidio",
        "avail_start": "19:00",
        "avail_end": "19:45",
        "min_duration": 45,
    },
    {
        "name": "Karen",
        "location": "Golden Gate Park",
        "avail_start": "19:30",
        "avail_end": "22:00",
        "min_duration": 120,
    },
    {
        "name": "Laura",
        "location": "Bayview",
        "avail_start": "21:15",
        "avail_end": "22:15",
        "min_duration": 15,
    },
]

# Preprocess time windows into minutes
for f in friends:
    f["avail_start_min"] = time_to_min(f["avail_start"])
    f["avail_end_min"] = time_to_min(f["avail_end"])

start_location = "Richmond District"
start_time_min = time_to_min("9:00")

n = len(friends)

# Z3 variables
x = [Bool(f"x_{i}") for i in range(n)]           # whether we meet friend i
s = [Int(f"s_{i}") for i in range(n)]            # meeting start time in minutes
e = [Int(f"e_{i}") for i in range(n)]            # meeting end time in minutes
first = [Bool(f"first_{i}") for i in range(n)]   # whether friend i is the first meeting

# Order variables for pairs i<j: o_ij == True means i before j
o = {}
for i in range(n):
    for j in range(i+1, n):
        o[(i, j)] = Bool(f"o_{i}_{j}")

opt = Optimize()
opt.set("priority", "lex")

# Time bounds
for i in range(n):
    opt.add(s[i] >= 0, s[i] <= 24*60)
    opt.add(e[i] >= 0, e[i] <= 24*60)

# Meeting constraints
for i, f in enumerate(friends):
    min_dur = f["min_duration"]
    a_start = f["avail_start_min"]
    a_end = f["avail_end_min"]
    # If meeting, must be within availability and meet minimum duration
    opt.add(Implies(x[i], And(s[i] >= a_start, e[i] <= a_end, e[i] - s[i] >= min_dur)))
    # If not meeting, collapse interval
    opt.add(Implies(Not(x[i]), e[i] == s[i]))

# Pairwise ordering and travel time constraints
def travel_time(loc_from, loc_to):
    if loc_from == loc_to:
        return 0
    return travel[loc_from][loc_to]

for i in range(n):
    for j in range(i+1, n):
        loc_i = friends[i]["location"]
        loc_j = friends[j]["location"]
        tij = travel_time(loc_i, loc_j)
        tji = travel_time(loc_j, loc_i)
        # If both visited and i before j, then j starts after i ends + travel
        opt.add(Implies(And(x[i], x[j], o[(i, j)]), s[j] >= e[i] + tij))
        # If both visited and j before i, then i starts after j ends + travel
        opt.add(Implies(And(x[i], x[j], Not(o[(i, j)])), s[i] >= e[j] + tji))
        # If one or both not visited, ordering var is irrelevant (no constraint)

# First meeting constraints
# - first[i] implies we meet i
for i in range(n):
    opt.add(Implies(first[i], x[i]))
# - Exactly one first if we meet at least one friend, else none
sum_x = Sum([If(x[i], 1, 0) for i in range(n)])
sum_first = Sum([If(first[i], 1, 0) for i in range(n)])
opt.add(sum_first == If(sum_x >= 1, 1, 0))

# - If i is first, its start time is after departure from start location including travel
for i in range(n):
    tstart_i = travel_time(start_location, friends[i]["location"])
    opt.add(Implies(first[i], s[i] >= start_time_min + tstart_i))

# - If i is first and j is visited, then i must be before j in the pairwise order
for i in range(n):
    for j in range(n):
        if i == j:
            continue
        # i before j
        if i < j:
            opt.add(Implies(And(first[i], x[j]), o[(i, j)]))
        else:
            # i > j: i before j means Not(o[j, i])
            opt.add(Implies(And(first[i], x[j]), Not(o[(j, i)])))

# Objective: maximize number of friends met
obj_meet = opt.maximize(sum_x)

# Solve
if opt.check() != sat:
    # If unsat (shouldn't happen), output empty itinerary
    print(json.dumps({"itinerary": []}, indent=2))
    raise SystemExit

m = opt.model()

# Extract solution
schedule = []
for i in range(n):
    if is_true(m[x[i]]):
        start_m = m[s[i]].as_long()
        end_m = m[e[i]].as_long()
        schedule.append({
            "idx": i,
            "person": friends[i]["name"],
            "location": friends[i]["location"],
            "start": start_m,
            "end": end_m
        })

# Sort by start time
schedule.sort(key=lambda it: it["start"])

# Build itinerary output
itinerary = []
for it in schedule:
    itinerary.append({
        "action": "meet",
        "location": it["location"],
        "person": it["person"],
        "start_time": min_to_time(it["start"]),
        "end_time": min_to_time(it["end"])
    })

print(json.dumps({"itinerary": itinerary}, indent=2))