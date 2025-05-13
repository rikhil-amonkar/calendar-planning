from z3 import *
from itertools import combinations

friends = [
    {'name': 'Start', 'location': 'Sunset District', 'available_start': 540, 'available_end': 540, 'duration': 0},
    {'name': 'Charles', 'location': 'Presidio', 'available_start': 795, 'available_end': 900, 'duration': 105},
    {'name': 'Robert', 'location': 'Nob Hill', 'available_start': 795, 'available_end': 1050, 'duration': 90},
    {'name': 'Nancy', 'location': 'Pacific Heights', 'available_start': 1005, 'available_end': 1260, 'duration': 105},
    {'name': 'Brian', 'location': 'Mission District', 'available_start': 1050, 'available_end': 1260, 'duration': 60},
    {'name': 'Kimberly', 'location': 'Marina District', 'available_start': 1140, 'available_end': 1245, 'duration': 75},
    {'name': 'David', 'location': 'North Beach', 'available_start': 1005, 'available_end': 1110, 'duration': 75},
    {'name': 'William', 'location': 'Russian Hill', 'available_start': 750, 'available_end': 1155, 'duration': 120},
    {'name': 'Jeffrey', 'location': 'Richmond District', 'available_start': 720, 'available_end': 1155, 'duration': 45},
    {'name': 'Karen', 'location': 'Embarcadero', 'available_start': 855, 'available_end': 1245, 'duration': 60},
    {'name': 'Joshua', 'location': 'Alamo Square', 'available_start': 1185, 'available_end': 1260, 'duration': 60},
]

# Create Z3 variables for each friend
for friend in friends:
    friend['met'] = Bool(friend['name'])
    friend['start'] = Int(f'start_{friend["name"]}')
    friend['end'] = Int(f'end_{friend["name"]}')

travel_time = {
    ('Sunset District', 'Presidio'): 16,
    ('Sunset District', 'Nob Hill'): 27,
    ('Sunset District', 'Pacific Heights'): 21,
    ('Sunset District', 'Mission District'): 25,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'North Beach'): 28,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Richmond District'): 12,
    ('Sunset District', 'Embarcadero'): 30,
    ('Sunset District', 'Alamo Square'): 17,
    ('Presidio', 'Sunset District'): 15,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'Pacific Heights'): 11,
    ('Presidio', 'Mission District'): 26,
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Alamo Square'): 19,
    ('Nob Hill', 'Sunset District'): 24,
    ('Nob Hill', 'Presidio'): 17,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'Mission District'): 13,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'Richmond District'): 14,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Nob Hill', 'Alamo Square'): 11,
    ('Pacific Heights', 'Sunset District'): 21,
    ('Pacific Heights', 'Presidio'): 11,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Marina District'): 6,
    ('Pacific Heights', 'North Beach'): 9,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Pacific Heights', 'Richmond District'): 12,
    ('Pacific Heights', 'Embarcadero'): 10,
    ('Pacific Heights', 'Alamo Square'): 10,
    ('Mission District', 'Sunset District'): 24,
    ('Mission District', 'Presidio'): 25,
    ('Mission District', 'Nob Hill'): 12,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Marina District'): 19,
    ('Mission District', 'North Beach'): 17,
    ('Mission District', 'Russian Hill'): 15,
    ('Mission District', 'Richmond District'): 20,
    ('Mission District', 'Embarcadero'): 19,
    ('Mission District', 'Alamo Square'): 11,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'Mission District'): 20,
    ('Marina District', 'North Beach'): 11,
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Embarcadero'): 14,
    ('Marina District', 'Alamo Square'): 15,
    ('North Beach', 'Sunset District'): 27,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Pacific Heights'): 8,
    ('North Beach', 'Mission District'): 18,
    ('North Beach', 'Marina District'): 9,
    ('North Beach', 'Russian Hill'): 4,
    ('North Beach', 'Richmond District'): 18,
    ('North Beach', 'Embarcadero'): 6,
    ('North Beach', 'Alamo Square'): 16,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Russian Hill', 'Mission District'): 16,
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'Richmond District'): 14,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Richmond District', 'Sunset District'): 11,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Nob Hill'): 17,
    ('Richmond District', 'Pacific Heights'): 10,
    ('Richmond District', 'Mission District'): 20,
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'North Beach'): 17,
    ('Richmond District', 'Russian Hill'): 13,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Alamo Square'): 13,
    ('Embarcadero', 'Sunset District'): 30,
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Pacific Heights'): 11,
    ('Embarcadero', 'Mission District'): 20,
    ('Embarcadero', 'Marina District'): 12,
    ('Embarcadero', 'North Beach'): 5,
    ('Embarcadero', 'Russian Hill'): 8,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Presidio'): 17,
    ('Alamo Square', 'Nob Hill'): 11,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Alamo Square', 'Mission District'): 10,
    ('Alamo Square', 'Marina District'): 15,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'Richmond District'): 11,
    ('Alamo Square', 'Embarcadero'): 16,
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
    if a['name'] == 'Start' or b['name'] == 'Start':
        continue  # Already handled start location travel
    travel_ab = travel_time.get((a['location'], b['location']), None)
    travel_ba = travel_time.get((b['location'], a['location']), None)
    if not travel_ab or not travel_ba:
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