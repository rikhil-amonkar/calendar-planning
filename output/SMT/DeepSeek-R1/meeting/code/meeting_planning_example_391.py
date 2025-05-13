from z3 import *
from itertools import combinations

friends = [
    {'name': 'Start', 'location': 'Sunset District', 'available_start': 540, 'available_end': 540, 'duration': 0},
    {'name': 'Kevin', 'location': 'Alamo Square', 'available_start': 495, 'available_end': 1290, 'duration': 75},
    {'name': 'Kimberly', 'location': 'Russian Hill', 'available_start': 525, 'available_end': 750, 'duration': 30},
    {'name': 'Joseph', 'location': 'Presidio', 'available_start': 1110, 'available_end': 1155, 'duration': 45},
    {'name': 'Thomas', 'location': 'Financial District', 'available_start': 1140, 'available_end': 1305, 'duration': 45},
]

for friend in friends:
    friend['met'] = Bool(friend['name'])
    friend['start'] = Int(f'start_{friend["name"]}')
    friend['end'] = Int(f'end_{friend["name"]}')

travel_time = {
    ('Sunset District', 'Alamo Square'): 17,
    ('Alamo Square', 'Sunset District'): 16,
    ('Sunset District', 'Russian Hill'): 24,
    ('Russian Hill', 'Sunset District'): 23,
    ('Sunset District', 'Presidio'): 16,
    ('Presidio', 'Sunset District'): 15,
    ('Sunset District', 'Financial District'): 30,
    ('Financial District', 'Sunset District'): 31,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Alamo Square', 'Presidio'): 18,
    ('Presidio', 'Alamo Square'): 18,
    ('Alamo Square', 'Financial District'): 17,
    ('Financial District', 'Alamo Square'): 17,
    ('Russian Hill', 'Presidio'): 14,
    ('Presidio', 'Russian Hill'): 14,
    ('Russian Hill', 'Financial District'): 11,
    ('Financial District', 'Russian Hill'): 10,
    ('Presidio', 'Financial District'): 23,
    ('Financial District', 'Presidio'): 22,
}

solver = Solver()

# Start must be met with fixed times
solver.add(friends[0]['met'] == True)
solver.add(friends[0]['start'] == 540)
solver.add(friends[0]['end'] == 540)

for friend in friends[1:]:
    met = friend['met']
    start = friend['start']
    end = friend['end']
    solver.add(Implies(met, start >= friend['available_start']))
    solver.add(Implies(met, end == start + friend['duration']))
    solver.add(Implies(met, end <= friend['available_end']))

# Add pairwise constraints including Start
for a, b in combinations(friends, 2):
    a_before_b = Bool(f"{a['name']}_before_{b['name']}")
    travel_ab = travel_time.get((a['location'], b['location']), None)
    travel_ba = travel_time.get((b['location'], a['location']), None)
    if travel_ab is None or travel_ba is None:
        continue
    solver.add(Implies(And(a['met'], b['met'], a_before_b), b['start'] >= a['end'] + travel_ab))
    solver.add(Implies(And(a['met'], b['met'], Not(a_before_b)), a['start'] >= b['end'] + travel_ba))

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