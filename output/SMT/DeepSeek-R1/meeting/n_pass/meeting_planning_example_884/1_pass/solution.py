import json
from z3 import *

# Define travel times between districts
travel_times = {
    "Richmond District": {
        "Richmond District": 0,
        "Chinatown": 20,
        "Sunset District": 11,
        "Alamo Square": 13,
        "Financial District": 22,
        "North Beach": 17,
        "Embarcadero": 19,
        "Presidio": 7,
        "Golden Gate Park": 9,
        "Bayview": 27
    },
    "Chinatown": {
        "Richmond District": 20,
        "Chinatown": 0,
        "Sunset District": 29,
        "Alamo Square": 17,
        "Financial District": 5,
        "North Beach": 3,
        "Embarcadero": 5,
        "Presidio": 19,
        "Golden Gate Park": 23,
        "Bayview": 20
    },
    "Sunset District": {
        "Richmond District": 12,
        "Chinatown": 30,
        "Sunset District": 0,
        "Alamo Square": 17,
        "Financial District": 30,
        "North Beach": 28,
        "Embarcadero": 30,
        "Presidio": 16,
        "Golden Gate Park": 11,
        "Bayview": 22
    },
    "Alamo Square": {
        "Richmond District": 11,
        "Chinatown": 15,
        "Sunset District": 16,
        "Alamo Square": 0,
        "Financial District": 17,
        "North Beach": 15,
        "Embarcadero": 16,
        "Presidio": 17,
        "Golden Gate Park": 9,
        "Bayview": 16
    },
    "Financial District": {
        "Richmond District": 21,
        "Chinatown": 5,
        "Sunset District": 30,
        "Alamo Square": 17,
        "Financial District": 0,
        "North Beach": 7,
        "Embarcadero": 4,
        "Presidio": 22,
        "Golden Gate Park": 23,
        "Bayview": 19
    },
    "North Beach": {
        "Richmond District": 18,
        "Chinatown": 6,
        "Sunset District": 27,
        "Alamo Square": 16,
        "Financial District": 8,
        "North Beach": 0,
        "Embarcadero": 6,
        "Presidio": 17,
        "Golden Gate Park": 22,
        "Bayview": 25
    },
    "Embarcadero": {
        "Richmond District": 21,
        "Chinatown": 7,
        "Sunset District": 30,
        "Alamo Square": 19,
        "Financial District": 5,
        "North Beach": 5,
        "Embarcadero": 0,
        "Presidio": 20,
        "Golden Gate Park": 25,
        "Bayview": 21
    },
    "Presidio": {
        "Richmond District": 7,
        "Chinatown": 21,
        "Sunset District": 15,
        "Alamo Square": 19,
        "Financial District": 23,
        "North Beach": 18,
        "Embarcadero": 20,
        "Presidio": 0,
        "Golden Gate Park": 12,
        "Bayview": 31
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
        "Golden Gate Park": 0,
        "Bayview": 23
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
        "Bayview": 0
    }
}

# Define friends and their constraints
friends = [
    {'name': 'Robert', 'location': 'Chinatown', 'start_avail': 7*60+45, 'end_avail': 17*60+30, 'min_dur': 120},
    {'name': 'David', 'location': 'Sunset District', 'start_avail': 12*60+30, 'end_avail': 19*60+45, 'min_dur': 45},
    {'name': 'Matthew', 'location': 'Alamo Square', 'start_avail': 8*60+45, 'end_avail': 13*60+45, 'min_dur': 90},
    {'name': 'Jessica', 'location': 'Financial District', 'start_avail': 9*60+30, 'end_avail': 18*60+45, 'min_dur': 45},
    {'name': 'Melissa', 'location': 'North Beach', 'start_avail': 7*60+15, 'end_avail': 16*60+45, 'min_dur': 45},
    {'name': 'Mark', 'location': 'Embarcadero', 'start_avail': 15*60+15, 'end_avail': 17*60+00, 'min_dur': 45},
    {'name': 'Deborah', 'location': 'Presidio', 'start_avail': 19*60+00, 'end_avail': 19*60+45, 'min_dur': 45},
    {'name': 'Karen', 'location': 'Golden Gate Park', 'start_avail': 19*60+30, 'end_avail': 22*60+00, 'min_dur': 120},
    {'name': 'Laura', 'location': 'Bayview', 'start_avail': 21*60+15, 'end_avail': 22*60+15, 'min_dur': 15}
]

n = len(friends)

# Initialize Z3 solver and variables
s = Solver()
opt = Optimize()

include = [Bool(f"include_{i}") for i in range(n)]
start = [Int(f"start_{i}") for i in range(n)]
before = [[Bool(f"before_{i}_{j}") for j in range(n)] for i in range(n)]

# Add constraints
for i in range(n):
    loc_i = friends[i]['location']
    travel_from_richmond = travel_times['Richmond District'][loc_i]
    s.add(Implies(include[i], start[i] >= friends[i]['start_avail']))
    s.add(Implies(include[i], start[i] + friends[i]['min_dur'] <= friends[i]['end_avail']))
    s.add(Implies(include[i], start[i] >= 540 + travel_from_richmond))

for i in range(n):
    for j in range(n):
        if i == j:
            continue
        loc_i = friends[i]['location']
        loc_j = friends[j]['location']
        travel_ij = travel_times[loc_i][loc_j]
        travel_ji = travel_times[loc_j][loc_i]
        both_included = And(include[i], include[j])
        cond1 = And(before[i][j], start[j] >= start[i] + friends[i]['min_dur'] + travel_ij)
        cond2 = And(before[j][i], start[i] >= start[j] + friends[j]['min_dur'] + travel_ji)
        s.add(Implies(both_included, Or(cond1, cond2)))
        s.add(Implies(both_included, before[i][j] == Not(before[j][i])))

total_meetings = Sum([If(include[i], 1, 0) for i in range(n)])
opt.add(s.assertions())
opt.maximize(total_meetings)

# Solve and output
itinerary = []
if opt.check() == sat:
    m = opt.model()
    for i in range(n):
        if is_true(m.eval(include[i])):
            start_val = m.eval(start[i])
            if isinstance(start_val, IntNumRef):
                start_min = start_val.as_long()
            else:
                start_min = start_val
            end_min = start_min + friends[i]['min_dur']
            start_hour = start_min // 60
            start_minute = start_min % 60
            end_hour = end_min // 60
            end_minute = end_min % 60
            start_str = f"{start_hour:02d}:{start_minute:02d}"
            end_str = f"{end_hour:02d}:{end_minute:02d}"
            itinerary.append({
                "action": "meet",
                "person": friends[i]['name'],
                "start_time": start_str,
                "end_time": end_str
            })
    itinerary.sort(key=lambda x: x['start_time'])
else:
    itinerary = []

print("SOLUTION:")
print(json.dumps({'itinerary': itinerary}))