from z3 import *
import json

# Define the friends and their constraints
friends = [
    {'name': 'Charles', 'district': 'Bayview', 'start_win': 11.5*60, 'end_win': 14.5*60, 'min_dur': 45},
    {'name': 'Robert', 'district': 'Sunset District', 'start_win': 16.75*60, 'end_win': 21*60, 'min_dur': 30},
    {'name': 'Karen', 'district': 'Richmond District', 'start_win': 19.25*60, 'end_win': 21.5*60, 'min_dur': 60},
    {'name': 'Rebecca', 'district': 'Nob Hill', 'start_win': 16.25*60, 'end_win': 20.5*60, 'min_dur': 90},
    {'name': 'Margaret', 'district': 'Chinatown', 'start_win': 14.25*60, 'end_win': 19.75*60, 'min_dur': 120},
    {'name': 'Patricia', 'district': 'Haight-Ashbury', 'start_win': 14.5*60, 'end_win': 20.5*60, 'min_dur': 45},
    {'name': 'Mark', 'district': 'North Beach', 'start_win': 14*60, 'end_win': 18.5*60, 'min_dur': 105},
    {'name': 'Melissa', 'district': 'Russian Hill', 'start_win': 13*60, 'end_win': 19.75*60, 'min_dur': 30},
    {'name': 'Laura', 'district': 'Embarcadero', 'start_win': 7.75*60, 'end_win': 13.25*60, 'min_dur': 105}
]

# Build the travel time dictionary
travel_dict = {
    "Marina District": {
        "Bayview": 27, "Sunset District": 19, "Richmond District": 11, "Nob Hill": 12,
        "Chinatown": 15, "Haight-Ashbury": 16, "North Beach": 11, "Russian Hill": 8, "Embarcadero": 14
    },
    "Bayview": {
        "Marina District": 27, "Sunset District": 23, "Richmond District": 25, "Nob Hill": 20,
        "Chinatown": 19, "Haight-Ashbury": 19, "North Beach": 22, "Russian Hill": 23, "Embarcadero": 19
    },
    "Sunset District": {
        "Marina District": 21, "Bayview": 22, "Richmond District": 12, "Nob Hill": 27,
        "Chinatown": 30, "Haight-Ashbury": 15, "North Beach": 28, "Russian Hill": 24, "Embarcadero": 30
    },
    "Richmond District": {
        "Marina District": 9, "Bayview": 27, "Sunset District": 11, "Nob Hill": 17,
        "Chinatown": 20, "Haight-Ashbury": 10, "North Beach": 17, "Russian Hill": 13, "Embarcadero": 19
    },
    "Nob Hill": {
        "Marina District": 11, "Bayview": 19, "Sunset District": 24, "Richmond District": 14,
        "Chinatown": 6, "Haight-Ashbury": 13, "North Beach": 8, "Russian Hill": 5, "Embarcadero": 9
    },
    "Chinatown": {
        "Marina District": 12, "Bayview": 20, "Sunset District": 29, "Richmond District": 20,
        "Nob Hill": 9, "Haight-Ashbury": 19, "North Beach": 3, "Russian Hill": 7, "Embarcadero": 5
    },
    "Haight-Ashbury": {
        "Marina District": 17, "Bayview": 18, "Sunset District": 15, "Richmond District": 10,
        "Nob Hill": 15, "Chinatown": 19, "North Beach": 19, "Russian Hill": 17, "Embarcadero": 20
    },
    "North Beach": {
        "Marina District": 9, "Bayview": 25, "Sunset District": 27, "Richmond District": 18,
        "Nob Hill": 7, "Chinatown": 6, "Haight-Ashbury": 18, "Russian Hill": 4, "Embarcadero": 6
    },
    "Russian Hill": {
        "Marina District": 7, "Bayview": 23, "Sunset District": 23, "Richmond District": 14,
        "Nob Hill": 5, "Chinatown": 9, "Haight-Ashbury": 17, "North Beach": 5, "Embarcadero": 8
    },
    "Embarcadero": {
        "Marina District": 12, "Bayview": 21, "Sunset District": 30, "Richmond District": 21,
        "Nob Hill": 10, "Chinatown": 7, "Haight-Ashbury": 21, "North Beach": 5, "Russian Hill": 8
    }
}

n = len(friends)
s = Optimize()
s.set("timeout", 300000)  # 5 minutes timeout

# Variables
included = [Bool(f'included_{i}') for i in range(n)]
position = [Int(f'position_{i}') for i in range(n)]
start = [Int(f'start_{i}') for i in range(n)]
end = [Int(f'end_{i}') for i in range(n)]

# Constraints for each meeting
for i in range(n):
    # If included, enforce meeting constraints
    s.add(If(included[i],
             And(start[i] >= friends[i]['start_win'],
                 end[i] <= friends[i]['end_win'],
                 end[i] - start[i] >= friends[i]['min_dur'],
                 position[i] >= 0),
             And(position[i] == -1, start[i] == 0, end[i] == 0)  # Dummy values if not included
           ))

# Distinct positions for included meetings
for i in range(n):
    for j in range(i+1, n):
        s.add(If(And(included[i], included[j]), position[i] != position[j], True))

# At least one meeting at position 0 if any meeting is included
s.add(If(Or([included[i] for i in range(n)]),
          Or([And(included[i], position[i] == 0) for i in range(n)]),
          True))

# Travel constraints from Marina for the first meeting
for i in range(n):
    s.add(If(And(included[i], position[i] == 0),
             start[i] >= 9*60 + travel_dict['Marina District'][friends[i]['district']],
             True))

# Travel constraints between consecutive meetings
for i in range(n):
    for j in range(n):
        if i == j:
            continue
        s.add(If(And(included[i], included[j], position[j] == position[i] - 1),
                 start[i] >= end[j] + travel_dict[friends[j]['district']][friends[i]['district']],
                 True))

# Ensure a predecessor exists for non-first meetings
for i in range(n):
    cond = And(included[i], position[i] >= 1)
    disj = Or([And(included[j], position[j] == position[i] - 1) for j in range(n) if j != i])
    s.add(If(cond, disj, True))

# Maximize the number of included meetings
total_included = Sum([If(included[i], 1, 0) for i in range(n)])
s.maximize(total_included)

# Solve the problem
if s.check() == sat:
    m = s.model()
    num_meetings = m.eval(total_included).as_long()
    schedule = []
    for i in range(n):
        if m.eval(included[i]):
            start_val = m.eval(start[i]).as_long()
            end_val = m.eval(end[i]).as_long()
            pos_val = m.eval(position[i]).as_long()
            name = friends[i]['name']
            # Format start and end times to HH:MM
            start_hour = start_val // 60
            start_minute = start_val % 60
            end_hour = end_val // 60
            end_minute = end_val % 60
            start_str = f"{start_hour:02d}:{start_minute:02d}"
            end_str = f"{end_hour:02d}:{end_minute:02d}"
            schedule.append((pos_val, {
                "action": "meet",
                "person": name,
                "start_time": start_str,
                "end_time": end_str
            }))
    # Sort by position
    schedule.sort(key=lambda x: x[0])
    itinerary = [entry for _, entry in schedule]
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print('{"itinerary": []}')