import json
from z3 import *

def tm(h, m):
    return h*60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Locations
locations = [
    "Nob Hill",
    "Embarcadero",
    "The Castro",
    "Haight-Ashbury",
    "Union Square",
    "North Beach",
    "Pacific Heights",
    "Chinatown",
    "Golden Gate Park",
    "Marina District",
    "Russian Hill",
]

# Directed travel times (minutes)
T = {loc: {} for loc in locations}
# Nob Hill ->
T["Nob Hill"].update({
    "Embarcadero": 9,
    "The Castro": 17,
    "Haight-Ashbury": 13,
    "Union Square": 7,
    "North Beach": 8,
    "Pacific Heights": 8,
    "Chinatown": 6,
    "Golden Gate Park": 17,
    "Marina District": 11,
    "Russian Hill": 5
})
# Embarcadero ->
T["Embarcadero"].update({
    "Nob Hill": 10,
    "The Castro": 25,
    "Haight-Ashbury": 21,
    "Union Square": 10,
    "North Beach": 5,
    "Pacific Heights": 11,
    "Chinatown": 7,
    "Golden Gate Park": 25,
    "Marina District": 12,
    "Russian Hill": 8
})
# The Castro ->
T["The Castro"].update({
    "Nob Hill": 16,
    "Embarcadero": 22,
    "Haight-Ashbury": 6,
    "Union Square": 19,
    "North Beach": 20,
    "Pacific Heights": 16,
    "Chinatown": 22,
    "Golden Gate Park": 11,
    "Marina District": 21,
    "Russian Hill": 18
})
# Haight-Ashbury ->
T["Haight-Ashbury"].update({
    "Nob Hill": 15,
    "Embarcadero": 20,
    "The Castro": 6,
    "Union Square": 19,
    "North Beach": 19,
    "Pacific Heights": 12,
    "Chinatown": 19,
    "Golden Gate Park": 7,
    "Marina District": 17,
    "Russian Hill": 17
})
# Union Square ->
T["Union Square"].update({
    "Nob Hill": 9,
    "Embarcadero": 11,
    "The Castro": 17,
    "Haight-Ashbury": 18,
    "North Beach": 10,
    "Pacific Heights": 15,
    "Chinatown": 7,
    "Golden Gate Park": 22,
    "Marina District": 18,
    "Russian Hill": 13
})
# North Beach ->
T["North Beach"].update({
    "Nob Hill": 7,
    "Embarcadero": 6,
    "The Castro": 23,
    "Haight-Ashbury": 18,
    "Union Square": 7,
    "Pacific Heights": 8,
    "Chinatown": 6,
    "Golden Gate Park": 22,
    "Marina District": 9,
    "Russian Hill": 4
})
# Pacific Heights ->
T["Pacific Heights"].update({
    "Nob Hill": 8,
    "Embarcadero": 10,
    "The Castro": 16,
    "Haight-Ashbury": 11,
    "Union Square": 12,
    "North Beach": 9,
    "Chinatown": 11,
    "Golden Gate Park": 15,
    "Marina District": 6,
    "Russian Hill": 7
})
# Chinatown ->
T["Chinatown"].update({
    "Nob Hill": 9,
    "Embarcadero": 5,
    "The Castro": 22,
    "Haight-Ashbury": 19,
    "Union Square": 7,
    "North Beach": 3,
    "Pacific Heights": 10,
    "Golden Gate Park": 23,
    "Marina District": 12,
    "Russian Hill": 7
})
# Golden Gate Park ->
T["Golden Gate Park"].update({
    "Nob Hill": 20,
    "Embarcadero": 25,
    "The Castro": 13,
    "Haight-Ashbury": 7,
    "Union Square": 22,
    "North Beach": 23,
    "Pacific Heights": 16,
    "Chinatown": 23,
    "Marina District": 16,
    "Russian Hill": 19
})
# Marina District ->
T["Marina District"].update({
    "Nob Hill": 12,
    "Embarcadero": 14,
    "The Castro": 22,
    "Haight-Ashbury": 16,
    "Union Square": 16,
    "North Beach": 11,
    "Pacific Heights": 7,
    "Chinatown": 15,
    "Golden Gate Park": 18,
    "Russian Hill": 8
})
# Russian Hill ->
T["Russian Hill"].update({
    "Nob Hill": 5,
    "Embarcadero": 8,
    "The Castro": 21,
    "Haight-Ashbury": 17,
    "Union Square": 10,
    "North Beach": 5,
    "Pacific Heights": 7,
    "Chinatown": 9,
    "Golden Gate Park": 21,
    "Marina District": 7
})

# Fill zero for same location and ensure all directed pairs exist
for a in locations:
    T[a][a] = 0
for a in locations:
    for b in locations:
        if b not in T[a]:
            # If missing, set a large travel time to discourage/impossible paths
            # but we expect all pairs are provided in the problem statement.
            T[a][b] = 9999

# People and constraints
people = [
    {"name": "Mary", "location": "Embarcadero", "start": tm(20,0), "end": tm(21,15), "min_dur": 75},
    {"name": "Kenneth", "location": "The Castro", "start": tm(11,15), "end": tm(19,15), "min_dur": 30},
    {"name": "Joseph", "location": "Haight-Ashbury", "start": tm(20,0), "end": tm(22,0), "min_dur": 120},
    {"name": "Sarah", "location": "Union Square", "start": tm(11,45), "end": tm(14,30), "min_dur": 90},
    {"name": "Thomas", "location": "North Beach", "start": tm(19,15), "end": tm(19,45), "min_dur": 15},
    {"name": "Daniel", "location": "Pacific Heights", "start": tm(13,45), "end": tm(20,30), "min_dur": 15},
    {"name": "Richard", "location": "Chinatown", "start": tm(8,0), "end": tm(18,45), "min_dur": 30},
    {"name": "Mark", "location": "Golden Gate Park", "start": tm(17,30), "end": tm(21,30), "min_dur": 120},
    {"name": "David", "location": "Marina District", "start": tm(20,0), "end": tm(21,0), "min_dur": 60},
    {"name": "Karen", "location": "Russian Hill", "start": tm(13,15), "end": tm(18,30), "min_dur": 120},
]

start_location = "Nob Hill"
start_time = tm(9,0)

n = len(people)

opt = Optimize()

sel = [Bool(f"sel_{i}") for i in range(n)]
s = [Int(f"s_{i}") for i in range(n)]
e = [Int(f"e_{i}") for i in range(n)]
d = [Int(f"d_{i}") for i in range(n)]

# Time bounds
DAY_END = 24*60

for i in range(n):
    p = people[i]
    loc = p["location"]
    # Basic time relations
    opt.add(d[i] >= 0)
    opt.add(e[i] == s[i] + d[i])
    opt.add(s[i] >= 0, e[i] >= 0, s[i] <= DAY_END, e[i] <= DAY_END)
    # If selected, must be within availability window and meet min duration
    opt.add(Implies(sel[i], And(
        s[i] >= p["start"],
        e[i] <= p["end"],
        d[i] >= p["min_dur"]
    )))
    # If not selected, no duration
    opt.add(Implies(Not(sel[i]), d[i] == 0))
    # Start-of-day reachability: cannot start meeting before earliest possible from start
    travel_from_start = T[start_location][loc]
    opt.add(Implies(sel[i], s[i] >= start_time + travel_from_start))

# Pairwise disjunctive constraints with travel
for i in range(n):
    for j in range(i+1, n):
        loc_i = people[i]["location"]
        loc_j = people[j]["location"]
        tij = T[loc_i][loc_j]
        tji = T[loc_j][loc_i]
        before_ij = Bool(f"before_{i}_{j}")
        # If both selected, enforce ordering with travel time
        opt.add(Implies(And(sel[i], sel[j], before_ij), s[j] >= e[i] + tij))
        opt.add(Implies(And(sel[i], sel[j], Not(before_ij)), s[i] >= e[j] + tji))
        # If either not selected, no constraint needed (implications won't trigger)

# Objective: maximize number of meetings, then total meeting time
total_meetings = Sum([If(sel[i], 1, 0) for i in range(n)])
total_minutes = Sum(d)

opt.maximize(total_meetings)
opt.maximize(total_minutes)

if opt.check() != sat:
    # No feasible schedule
    print(json.dumps({"itinerary": []}, indent=2))
else:
    m = opt.model()
    schedule = []
    for i in range(n):
        if is_true(m.evaluate(sel[i])):
            si = m.evaluate(s[i]).as_long()
            ei = m.evaluate(e[i]).as_long()
            schedule.append({
                "person": people[i]["name"],
                "location": people[i]["location"],
                "start": si,
                "end": ei
            })
    # Sort by start time
    schedule.sort(key=lambda x: x["start"])
    itinerary = []
    for item in schedule:
        itinerary.append({
            "action": "meet",
            "location": item["location"],
            "person": item["person"],
            "start_time": fmt_time(item["start"]),
            "end_time": fmt_time(item["end"])
        })
    print(json.dumps({"itinerary": itinerary}, indent=2))