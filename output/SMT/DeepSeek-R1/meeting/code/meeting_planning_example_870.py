from z3 import *
from itertools import combinations

friends = [
    {'name': 'Start', 'location': 'Pacific Heights', 'available_start': 540, 'available_end': 540, 'duration': 0},
    {'name': 'Linda', 'location': 'Marina District', 'available_start': 1080, 'available_end': 1320, 'duration': 30},
    {'name': 'Kenneth', 'location': 'The Castro', 'available_start': 885, 'available_end': 975, 'duration': 30},
    {'name': 'Kimberly', 'location': 'Richmond District', 'available_start': 855, 'available_end': 1320, 'duration': 30},
    {'name': 'Paul', 'location': 'Alamo Square', 'available_start': 1260, 'available_end': 1290, 'duration': 15},
    {'name': 'Carol', 'location': 'Financial District', 'available_start': 615, 'available_end': 720, 'duration': 60},
    {'name': 'Brian', 'location': 'Presidio', 'available_start': 600, 'available_end': 1290, 'duration': 75},
    {'name': 'Laura', 'location': 'Mission District', 'available_start': 975, 'available_end': 1230, 'duration': 30},
    {'name': 'Sandra', 'location': 'Nob Hill', 'available_start': 555, 'available_end': 1110, 'duration': 60},
    {'name': 'Karen', 'location': 'Russian Hill', 'available_start': 1110, 'available_end': 1320, 'duration': 75},
]

for friend in friends:
    friend['met'] = Bool(friend['name'])
    friend['start'] = Int(f'start_{friend["name"]}')
    friend['end'] = Int(f'end_{friend["name"]}')

travel_time = {
    ('Pacific Heights', 'Marina District'): 6,
    ('Pacific Heights', 'The Castro'): 16,
    ('Pacific Heights', 'Richmond District'): 12,
    ('Pacific Heights', 'Alamo Square'): 10,
    ('Pacific Heights', 'Financial District'): 13,
    ('Pacific Heights', 'Presidio'): 11,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'Mission District'): 20,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Russian Hill'): 8,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'Richmond District'): 16,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Financial District'): 21,
    ('The Castro', 'Presidio'): 20,
    ('The Castro', 'Mission District'): 7,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Russian Hill'): 18,
    ('Richmond District', 'Pacific Heights'): 10,
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'The Castro'): 16,
    ('Richmond District', 'Alamo Square'): 13,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Mission District'): 20,
    ('Richmond District', 'Nob Hill'): 17,
    ('Richmond District', 'Russian Hill'): 13,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Alamo Square', 'Marina District'): 15,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Richmond District'): 11,
    ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'Presidio'): 17,
    ('Alamo Square', 'Mission District'): 10,
    ('Alamo Square', 'Nob Hill'): 11,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'The Castro'): 20,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Mission District'): 17,
    ('Financial District', 'Nob Hill'): 8,
    ('Financial District', 'Russian Hill'): 11,
    ('Presidio', 'Pacific Heights'): 11,
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'The Castro'): 21,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Alamo Square'): 19,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'Mission District'): 26,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'Russian Hill'): 14,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Marina District'): 19,
    ('Mission District', 'The Castro'): 7,
    ('Mission District', 'Richmond District'): 20,
    ('Mission District', 'Alamo Square'): 11,
    ('Mission District', 'Financial District'): 15,
    ('Mission District', 'Presidio'): 25,
    ('Mission District', 'Nob Hill'): 12,
    ('Mission District', 'Russian Hill'): 15,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Richmond District'): 14,
    ('Nob Hill', 'Alamo Square'): 11,
    ('Nob Hill', 'Financial District'): 9,
    ('Nob Hill', 'Presidio'): 17,
    ('Nob Hill', 'Mission District'): 13,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Richmond District'): 14,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Financial District'): 11,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Mission District'): 16,
    ('Russian Hill', 'Nob Hill'): 5,
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