from z3 import *
import json

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hours = int(parts[0])
    minutes = int(parts[1])
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

locations_list = [
    "The Castro",
    "North Beach",
    "Golden Gate Park",
    "Embarcadero",
    "Haight-Ashbury",
    "Richmond District",
    "Nob Hill",
    "Marina District",
    "Presidio",
    "Union Square",
    "Financial District"
]

locations_index = {loc: idx for idx, loc in enumerate(locations_list)}

travel_matrix = [
    [0, 20, 11, 22, 6, 16, 16, 21, 20, 19, 21],
    [23, 0, 22, 6, 18, 18, 7, 9, 17, 7, 8],
    [13, 23, 0, 25, 7, 7, 20, 16, 11, 22, 26],
    [25, 5, 25, 0, 21, 21, 10, 12, 20, 10, 5],
    [6, 19, 7, 20, 0, 10, 15, 17, 15, 19, 21],
    [16, 17, 9, 19, 10, 0, 17, 9, 7, 21, 22],
    [17, 8, 17, 9, 13, 14, 0, 11, 17, 7, 9],
    [22, 11, 18, 14, 16, 11, 12, 0, 10, 16, 17],
    [21, 18, 12, 20, 15, 7, 18, 11, 0, 22, 23],
    [17, 10, 22, 11, 18, 20, 9, 18, 24, 0, 9],
    [20, 7, 23, 4, 19, 21, 8, 15, 22, 9, 0]
]

friends_data = [
    {"name": "Steven", "location": "North Beach", "available_start": "17:30", "available_end": "20:30", "min_duration": 15},
    {"name": "Sarah", "location": "Golden Gate Park", "available_start": "17:00", "available_end": "19:15", "min_duration": 75},
    {"name": "Brian", "location": "Embarcadero", "available_start": "14:15", "available_end": "16:00", "min_duration": 105},
    {"name": "Stephanie", "location": "Haight-Ashbury", "available_start": "10:15", "available_end": "12:15", "min_duration": 75},
    {"name": "Melissa", "location": "Richmond District", "available_start": "14:00", "available_end": "19:30", "min_duration": 30},
    {"name": "Nancy", "location": "Nob Hill", "available_start": "8:15", "available_end": "12:45", "min_duration": 90},
    {"name": "David", "location": "Marina District", "available_start": "11:15", "available_end": "13:15", "min_duration": 120},
    {"name": "James", "location": "Presidio", "available_start": "15:00", "available_end": "18:15", "min_duration": 120},
    {"name": "Elizabeth", "location": "Union Square", "available_start": "11:30", "available_end": "21:00", "min_duration": 60},
    {"name": "Robert", "location": "Financial District", "available_start": "13:15", "available_end": "15:15", "min_duration": 45}
]

for friend in friends_data:
    friend['available_start_min'] = time_to_minutes(friend['available_start'])
    friend['available_end_min'] = time_to_minutes(friend['available_end'])
    friend['loc_index'] = locations_index[friend['location']]

solver = Optimize()

n_friends = 10
n_total = n_friends + 1  
s = [Int(f's_{i}') for i in range(n_total)]
met = [Bool(f'met_{i}') for i in range(n_total)]
durations = [0] * n_total
locations = [0] * n_total

dummy_index = n_friends
solver.add(met[dummy_index] == True)
solver.add(s[dummy_index] == 540)
durations[dummy_index] = 0
locations[dummy_index] = 0

for i in range(n_friends):
    locations[i] = friends_data[i]['loc_index']
    durations[i] = friends_data[i]['min_duration']

    solver.add(Implies(met[i], s[i] >= friends_data[i]['available_start_min']))
    solver.add(Implies(met[i], s[i] + durations[i] <= friends_data[i]['available_end_min']))

solver.add(met[2] == True)
solver.add(s[2] == 855)
solver.add(met[6] == True)
solver.add(s[6] == 675)

for i in range(n_total):
    for j in range(n_total):
        if i != j:
            both_met = And(met[i], met[j])
            constraint = Or(
                s[i] + durations[i] + travel_matrix[locations[i]][locations[j]] <= s[j],
                s[j] + durations[j] + travel_matrix[locations[j]][locations[i]] <= s[i]
            )
            solver.add(Implies(both_met, constraint))

total_met = Sum([If(met[i], 1, 0) for i in range(n_friends)])
solver.maximize(total_met)

if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for i in range(n_friends):
        if is_true(model.eval(met[i])):
            start_val = model.eval(s[i]).as_long()
            end_val = start_val + friends_data[i]['min_duration']
            start_time = minutes_to_time(start_val)
            end_time = minutes_to_time(end_val)
            itinerary.append({
                "action": "meet",
                "person": friends_data[i]['name'],
                "start_time": start_time,
                "end_time": end_time
            })
    itinerary_sorted = sorted(itinerary, key=lambda x: time_to_minutes(x['start_time']))
    result = {"itinerary": itinerary_sorted}
    print(json.dumps(result, indent=2))
else:
    print('{"itinerary": []}')