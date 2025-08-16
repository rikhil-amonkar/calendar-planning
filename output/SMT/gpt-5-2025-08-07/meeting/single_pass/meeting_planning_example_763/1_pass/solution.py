from z3 import *
import json

def minutes_from_0900(hh_mm):
    hh, mm = map(int, hh_mm.split(":"))
    return (hh - 9) * 60 + mm

def minutes_to_time_str(mins_from_0900):
    total = mins_from_0900 + 9*60
    hh = total // 60
    mm = total % 60
    return f"{hh:02d}:{mm:02d}"

# Data
people = [
    {"name": "Richard",  "loc": "Embarcadero",        "start": minutes_from_0900("15:15"), "end": minutes_from_0900("18:45"), "dur": 90},
    {"name": "Mark",     "loc": "Pacific Heights",    "start": minutes_from_0900("15:00"), "end": minutes_from_0900("17:00"), "dur": 45},
    {"name": "Matthew",  "loc": "Russian Hill",       "start": minutes_from_0900("17:30"), "end": minutes_from_0900("21:00"), "dur": 90},
    {"name": "Rebecca",  "loc": "Haight-Ashbury",     "start": minutes_from_0900("14:45"), "end": minutes_from_0900("18:00"), "dur": 60},
    {"name": "Melissa",  "loc": "Golden Gate Park",   "start": minutes_from_0900("13:45"), "end": minutes_from_0900("17:30"), "dur": 90},
    {"name": "Margaret", "loc": "Fisherman's Wharf",  "start": minutes_from_0900("14:45"), "end": minutes_from_0900("20:15"), "dur": 15},
    {"name": "Emily",    "loc": "Sunset District",    "start": minutes_from_0900("15:45"), "end": minutes_from_0900("17:00"), "dur": 45},
    {"name": "George",   "loc": "The Castro",         "start": minutes_from_0900("14:00"), "end": minutes_from_0900("16:15"), "dur": 75},
]

locations = [
    "Chinatown",
    "Embarcadero",
    "Pacific Heights",
    "Russian Hill",
    "Haight-Ashbury",
    "Golden Gate Park",
    "Fisherman's Wharf",
    "Sunset District",
    "The Castro",
]

# Travel times (minutes), asymmetric
dist = {loc: {} for loc in locations}
# From Chinatown
dist["Chinatown"]["Embarcadero"] = 5
dist["Chinatown"]["Pacific Heights"] = 10
dist["Chinatown"]["Russian Hill"] = 7
dist["Chinatown"]["Haight-Ashbury"] = 19
dist["Chinatown"]["Golden Gate Park"] = 23
dist["Chinatown"]["Fisherman's Wharf"] = 8
dist["Chinatown"]["Sunset District"] = 29
dist["Chinatown"]["The Castro"] = 22

# From Embarcadero
dist["Embarcadero"]["Chinatown"] = 7
dist["Embarcadero"]["Pacific Heights"] = 11
dist["Embarcadero"]["Russian Hill"] = 8
dist["Embarcadero"]["Haight-Ashbury"] = 21
dist["Embarcadero"]["Golden Gate Park"] = 25
dist["Embarcadero"]["Fisherman's Wharf"] = 6
dist["Embarcadero"]["Sunset District"] = 30
dist["Embarcadero"]["The Castro"] = 25

# From Pacific Heights
dist["Pacific Heights"]["Chinatown"] = 11
dist["Pacific Heights"]["Embarcadero"] = 10
dist["Pacific Heights"]["Russian Hill"] = 7
dist["Pacific Heights"]["Haight-Ashbury"] = 11
dist["Pacific Heights"]["Golden Gate Park"] = 15
dist["Pacific Heights"]["Fisherman's Wharf"] = 13
dist["Pacific Heights"]["Sunset District"] = 21
dist["Pacific Heights"]["The Castro"] = 16

# From Russian Hill
dist["Russian Hill"]["Chinatown"] = 9
dist["Russian Hill"]["Embarcadero"] = 8
dist["Russian Hill"]["Pacific Heights"] = 7
dist["Russian Hill"]["Haight-Ashbury"] = 17
dist["Russian Hill"]["Golden Gate Park"] = 21
dist["Russian Hill"]["Fisherman's Wharf"] = 7
dist["Russian Hill"]["Sunset District"] = 23
dist["Russian Hill"]["The Castro"] = 21

# From Haight-Ashbury
dist["Haight-Ashbury"]["Chinatown"] = 19
dist["Haight-Ashbury"]["Embarcadero"] = 20
dist["Haight-Ashbury"]["Pacific Heights"] = 12
dist["Haight-Ashbury"]["Russian Hill"] = 17
dist["Haight-Ashbury"]["Golden Gate Park"] = 7
dist["Haight-Ashbury"]["Fisherman's Wharf"] = 23
dist["Haight-Ashbury"]["Sunset District"] = 15
dist["Haight-Ashbury"]["The Castro"] = 6

# From Golden Gate Park
dist["Golden Gate Park"]["Chinatown"] = 23
dist["Golden Gate Park"]["Embarcadero"] = 25
dist["Golden Gate Park"]["Pacific Heights"] = 16
dist["Golden Gate Park"]["Russian Hill"] = 19
dist["Golden Gate Park"]["Haight-Ashbury"] = 7
dist["Golden Gate Park"]["Fisherman's Wharf"] = 24
dist["Golden Gate Park"]["Sunset District"] = 10
dist["Golden Gate Park"]["The Castro"] = 13

# From Fisherman's Wharf
dist["Fisherman's Wharf"]["Chinatown"] = 12
dist["Fisherman's Wharf"]["Embarcadero"] = 8
dist["Fisherman's Wharf"]["Pacific Heights"] = 12
dist["Fisherman's Wharf"]["Russian Hill"] = 7
dist["Fisherman's Wharf"]["Haight-Ashbury"] = 22
dist["Fisherman's Wharf"]["Golden Gate Park"] = 25
dist["Fisherman's Wharf"]["Sunset District"] = 27
dist["Fisherman's Wharf"]["The Castro"] = 27

# From Sunset District
dist["Sunset District"]["Chinatown"] = 30
dist["Sunset District"]["Embarcadero"] = 30
dist["Sunset District"]["Pacific Heights"] = 21
dist["Sunset District"]["Russian Hill"] = 24
dist["Sunset District"]["Haight-Ashbury"] = 15
dist["Sunset District"]["Golden Gate Park"] = 11
dist["Sunset District"]["Fisherman's Wharf"] = 29
dist["Sunset District"]["The Castro"] = 17

# From The Castro
dist["The Castro"]["Chinatown"] = 22
dist["The Castro"]["Embarcadero"] = 22
dist["The Castro"]["Pacific Heights"] = 16
dist["The Castro"]["Russian Hill"] = 18
dist["The Castro"]["Haight-Ashbury"] = 6
dist["The Castro"]["Golden Gate Park"] = 11
dist["The Castro"]["Fisherman's Wharf"] = 24
dist["The Castro"]["Sunset District"] = 17

# Helper to get travel time between two people's locations
def travel_time_between(p_i, p_j):
    return dist[p_i["loc"]][p_j["loc"]]

def travel_time_from_start(p_i):
    return dist["Chinatown"][p_i["loc"]]

N = len(people)
TMAX = minutes_from_0900("21:00")  # 12 hours -> 720

opt = Optimize()

# Variables
meet = [Bool(f"meet_{i}") for i in range(N)]
s = [Int(f"s_{i}") for i in range(N)]
e = [Int(f"e_{i}") for i in range(N)]
pos = [Int(f"pos_{i}") for i in range(N)]
start_to = [Bool(f"start_to_{i}") for i in range(N)]
follow = [[Bool(f"follow_{i}_{j}") if i != j else False for j in range(N)] for i in range(N)]

# Domains and meeting window constraints
for i, p in enumerate(people):
    opt.add(s[i] >= 0, s[i] <= TMAX)
    opt.add(e[i] >= 0, e[i] <= TMAX)
    opt.add(pos[i] >= 0, pos[i] <= N)
    # If meet -> respect availability and duration, have a positive position
    opt.add(Implies(meet[i], And(
        s[i] >= p["start"],
        e[i] <= p["end"],
        e[i] - s[i] >= p["dur"],
        pos[i] >= 1
    )))
    # If not meeting -> zeroed variables
    opt.add(Implies(Not(meet[i]), And(
        s[i] == 0,
        e[i] == 0,
        pos[i] == 0
    )))

# Start predecessor constraints: exactly one first if we meet anyone (we enforce exactly one)
opt.add(Sum([If(start_to[i], 1, 0) for i in range(N)]) == 1)
for i in range(N):
    # start_to implies we actually meet i
    opt.add(Implies(start_to[i], meet[i]))
    # If start_to, arrival from Chinatown travel time and position 1
    opt.add(Implies(start_to[i], And(
        s[i] >= travel_time_from_start(people[i]),
        pos[i] == 1
    )))

# Follow constraints: ordering, single chain, and timing between consecutive meetings
for i in range(N):
    # At most one successor if we meet i
    opt.add(Sum([If(follow[i][j], 1, 0) for j in range(N) if i != j]) <= If(meet[i], 1, 0))
    for j in range(N):
        if i == j:
            continue
        # follow[i][j] implies both are met, timing, and positions
        tij = travel_time_between(people[i], people[j])
        opt.add(Implies(follow[i][j], And(
            meet[i], meet[j],
            s[j] >= e[i] + tij,
            pos[j] == pos[i] + 1
        )))

# Each met meeting has exactly one predecessor: either start or some other met meeting
for j in range(N):
    incoming_from_others = Sum([If(follow[i][j], 1, 0) for i in range(N) if i != j])
    opt.add(incoming_from_others + If(start_to[j], 1, 0) == If(meet[j], 1, 0))

# Objective 1: maximize number of friends met
total_met = Sum([If(meet[i], 1, 0) for i in range(N)])
h1 = opt.maximize(total_met)

# Objective 2: maximize total meeting time (to prefer longer visits in ties)
total_meet_minutes = Sum([If(meet[i], e[i] - s[i], 0) for i in range(N)])
h2 = opt.maximize(total_meet_minutes)

# Objective 3: minimize total travel time along the chain (start + follow edges), to break further ties
total_travel = Sum(
    [If(start_to[i], travel_time_from_start(people[i]), 0) for i in range(N)]
    +
    [If(follow[i][j], travel_time_between(people[i], people[j]), 0)
     for i in range(N) for j in range(N) if i != j]
)
h3 = opt.minimize(total_travel)

# Ensure at least one meeting (to avoid degenerate start_to assignment)
opt.add(total_met >= 1)

# Solve
if opt.check() != sat:
    # If unsat, print empty itinerary
    print(json.dumps({"itinerary": []}))
    exit(0)

m = opt.model()

# Reconstruct the chain
index_by_name = {p["name"]: i for i, p in enumerate(people)}

# find first
first_idx = None
for i in range(N):
    if m.evaluate(start_to[i]).is_true():
        first_idx = i
        break

order = []
if first_idx is not None:
    cur = first_idx
    visited = set()
    while cur is not None and cur not in visited:
        if m.evaluate(meet[cur]).is_true():
            order.append(cur)
        visited.add(cur)
        next_cur = None
        for j in range(N):
            if cur != j and m.evaluate(follow[cur][j]).is_true():
                next_cur = j
                break
        cur = next_cur

# Build itinerary
itinerary = []
for idx in order:
    p = people[idx]
    start_str = minutes_to_time_str(m.evaluate(s[idx]).as_long())
    end_str = minutes_to_time_str(m.evaluate(e[idx]).as_long())
    itinerary.append({
        "action": "meet",
        "person": p["name"],
        "start_time": start_str,
        "end_time": end_str
    })

print(json.dumps({"itinerary": itinerary}))