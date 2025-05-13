from z3 import *
from itertools import combinations

friends = [
    {'name': 'Start', 'location': "Fisherman's Wharf", 'available_start': 540, 'available_end': 540, 'duration': 0},
    {'name': 'Thomas', 'location': 'Bayview', 'available_start': 930, 'available_end': 1110, 'duration': 120},
    {'name': 'Stephanie', 'location': 'Golden Gate Park', 'available_start': 1110, 'available_end': 1305, 'duration': 30},
    {'name': 'Laura', 'location': 'Nob Hill', 'available_start': 525, 'available_end': 975, 'duration': 30},
    {'name': 'Betty', 'location': 'Marina District', 'available_start': 1125, 'available_end': 1305, 'duration': 45},
    {'name': 'Patricia', 'location': 'Embarcadero', 'available_start': 1050, 'available_end': 1320, 'duration': 45},
]

for friend in friends:
    friend['met'] = Bool(friend['name'])
    friend['start'] = Int(f'start_{friend["name"]}')
    friend['end'] = Int(f'end_{friend["name"]}')

travel_time = {
    ("Fisherman's Wharf", 'Bayview'): 26,
    ("Fisherman's Wharf", 'Golden Gate Park'): 25,
    ("Fisherman's Wharf", 'Nob Hill'): 11,
    ("Fisherman's Wharf", 'Marina District'): 9,
    ("Fisherman's Wharf", 'Embarcadero'): 8,
    ('Bayview', "Fisherman's Wharf"): 25,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Bayview', 'Nob Hill'): 20,
    ('Bayview', 'Marina District'): 25,
    ('Bayview', 'Embarcadero'): 19,
    ('Golden Gate Park', "Fisherman's Wharf"): 24,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Nob Hill', "Fisherman's Wharf"): 11,
    ('Nob Hill', 'Bayview'): 19,
    ('Nob Hill', 'Golden Gate Park'): 17,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Marina District', "Fisherman's Wharf"): 10,
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Embarcadero'): 14,
    ('Embarcadero', "Fisherman's Wharf"): 6,
    ('Embarcadero', 'Bayview'): 21,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Marina District'): 12,
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