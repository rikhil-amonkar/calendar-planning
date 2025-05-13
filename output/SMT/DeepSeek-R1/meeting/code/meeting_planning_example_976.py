from z3 import *
from itertools import combinations

friends = [
    {'name': 'Start', 'location': 'Embarcadero', 'available_start': 540, 'available_end': 540, 'duration': 0},
    {'name': 'Matthew', 'location': 'Bayview', 'available_start': 1095, 'available_end': 1320, 'duration': 120},
    {'name': 'Karen', 'location': 'Chinatown', 'available_start': 1095, 'available_end': 1170, 'duration': 90},
    {'name': 'Sarah', 'location': 'Alamo Square', 'available_start': 1200, 'available_end': 1305, 'duration': 105},
    {'name': 'Jessica', 'location': 'Nob Hill', 'available_start': 990, 'available_end': 1065, 'duration': 120},
    {'name': 'Stephanie', 'location': 'Presidio', 'available_start': 450, 'available_end': 615, 'duration': 60},
    {'name': 'Mary', 'location': 'Union Square', 'available_start': 1005, 'available_end': 1170, 'duration': 60},
    {'name': 'Charles', 'location': 'The Castro', 'available_start': 990, 'available_end': 1320, 'duration': 105},
    {'name': 'Nancy', 'location': 'North Beach', 'available_start': 885, 'available_end': 1080, 'duration': 15},
    {'name': 'Thomas', 'location': 'Fisherman\'s Wharf', 'available_start': 810, 'available_end': 1020, 'duration': 30},
    {'name': 'Brian', 'location': 'Marina District', 'available_start': 735, 'available_end': 1080, 'duration': 60},
]

for friend in friends:
    friend['met'] = Bool(friend['name'])
    friend['start'] = Int(f'start_{friend["name"]}')
    friend['end'] = Int(f'end_{friend["name"]}')

travel_time = {
    ('Embarcadero', 'Bayview'): 21,
    ('Embarcadero', 'Chinatown'): 7,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Union Square'): 10,
    ('Embarcadero', 'The Castro'): 25,
    ('Embarcadero', 'North Beach'): 5,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Embarcadero', 'Marina District'): 12,
    ('Bayview', 'Embarcadero'): 19,
    ('Bayview', 'Chinatown'): 19,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'Nob Hill'): 20,
    ('Bayview', 'Presidio'): 32,
    ('Bayview', 'Union Square'): 18,
    ('Bayview', 'The Castro'): 19,
    ('Bayview', 'North Beach'): 22,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Marina District'): 27,
    ('Chinatown', 'Embarcadero'): 5,
    ('Chinatown', 'Bayview'): 20,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'Nob Hill'): 9,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'The Castro'): 22,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', 'Fisherman\'s Wharf'): 8,
    ('Chinatown', 'Marina District'): 12,
    ('Alamo Square', 'Embarcadero'): 16,
    ('Alamo Square', 'Bayview'): 16,
    ('Alamo Square', 'Chinatown'): 15,
    ('Alamo Square', 'Nob Hill'): 11,
    ('Alamo Square', 'Presidio'): 17,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Fisherman\'s Wharf'): 19,
    ('Alamo Square', 'Marina District'): 15,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Nob Hill', 'Bayview'): 19,
    ('Nob Hill', 'Chinatown'): 6,
    ('Nob Hill', 'Alamo Square'): 11,
    ('Nob Hill', 'Presidio'): 17,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Fisherman\'s Wharf'): 10,
    ('Nob Hill', 'Marina District'): 11,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Bayview'): 31,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'Alamo Square'): 19,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'The Castro'): 21,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Marina District'): 11,
    ('Union Square', 'Embarcadero'): 11,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'The Castro'): 17,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Fisherman\'s Wharf'): 15,
    ('Union Square', 'Marina District'): 18,
    ('The Castro', 'Embarcadero'): 22,
    ('The Castro', 'Bayview'): 19,
    ('The Castro', 'Chinatown'): 22,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Presidio'): 20,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'North Beach'): 20,
    ('The Castro', 'Fisherman\'s Wharf'): 24,
    ('The Castro', 'Marina District'): 21,
    ('North Beach', 'Embarcadero'): 6,
    ('North Beach', 'Bayview'): 25,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Alamo Square'): 16,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'The Castro'): 23,
    ('North Beach', 'Fisherman\'s Wharf'): 5,
    ('North Beach', 'Marina District'): 9,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Chinatown'): 12,
    ('Fisherman\'s Wharf', 'Alamo Square'): 21,
    ('Fisherman\'s Wharf', 'Nob Hill'): 11,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Union Square'): 13,
    ('Fisherman\'s Wharf', 'The Castro'): 27,
    ('Fisherman\'s Wharf', 'North Beach'): 6,
    ('Fisherman\'s Wharf', 'Marina District'): 9,
    ('Marina District', 'Embarcadero'): 14,
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Chinatown'): 15,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'North Beach'): 11,
    ('Marina District', 'Fisherman\'s Wharf'): 10,
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