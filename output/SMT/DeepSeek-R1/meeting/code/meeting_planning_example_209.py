from z3 import *
from itertools import combinations

friends = [
    {'name': 'Start', 'location': 'Sunset District', 'available_start': 540, 'available_end': 540, 'duration': 0},
    {'name': 'Anthony', 'location': 'Chinatown', 'available_start': 795, 'available_end': 900, 'duration': 60},
    {'name': 'Rebecca', 'location': 'Russian Hill', 'available_start': 1170, 'available_end': 1275, 'duration': 105},
    {'name': 'Melissa', 'location': 'North Beach', 'available_start': 495, 'available_end': 810, 'duration': 105},
]

for friend in friends:
    friend['met'] = Bool(friend['name'])
    friend['start'] = Int(f'start_{friend["name"]}')
    friend['end'] = Int(f'end_{friend["name"]}')

travel_time = {
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'North Beach'): 29,
    ('Chinatown', 'Sunset District'): 29,
    ('Chinatown', 'Russian Hill'): 7,
    ('Chinatown', 'North Beach'): 3,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'North Beach'): 5,
    ('North Beach', 'Sunset District'): 27,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Russian Hill'): 4,
}

solver = Solver()

# Start constraints
solver.add(friends[0]['met'] == True)
solver.add(friends[0]['start'] == 540)
solver.add(friends[0]['end'] == 540)

# Friend constraints
for friend in friends[1:]:
    met = friend['met']
    start = friend['start']
    end = friend['end']
    # Time window and duration constraints
    solver.add(Implies(met, start >= friend['available_start']))
    solver.add(Implies(met, end == start + friend['duration']))
    solver.add(Implies(met, end <= friend['available_end']))
    # Travel time from start location
    travel_start = travel_time.get(('Sunset District', friend['location']), 0)
    solver.add(Implies(met, start >= 540 + travel_start))

# Meeting order constraints
for a, b in combinations(friends, 2):
    travel_ab = travel_time.get((a['location'], b['location']), None)
    travel_ba = travel_time.get((b['location'], a['location']), None)
    if travel_ab is None or travel_ba is None:
        continue
    solver.add(Implies(And(a['met'], b['met']),
               Or(b['start'] >= a['end'] + travel_ab,
                  a['start'] >= b['end'] + travel_ba)))

# Maximize number of friends met
max_friends = Sum([If(f['met'], 1, 0) for f in friends[1:]])
solver.maximize(max_friends)

if solver.check() == sat:
    model = solver.model()
    schedule = []
    for friend in friends[1:]:
        if model.eval(friend['met']):
            start = model.eval(friend['start']).as_long()
            end = model.eval(friend['end']).as_long()
            schedule.append((friend['name'], start, end))
    schedule.sort(key=lambda x: x[1])
    print("Optimal Schedule:")
    for name, s, e in schedule:
        print(f"{name}: {s//60:02d}:{s%60:02d}-{e//60:02d}:{e%60:02d}")
else:
    print("No valid schedule found.")