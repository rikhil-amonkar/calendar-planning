from z3 import *
from itertools import combinations

friends = [
    {'name': 'Start', 'location': 'Richmond District', 'available_start': 540, 'available_end': 540, 'duration': 0},
    {'name': 'Robert', 'location': 'Chinatown', 'available_start': 465, 'available_end': 1050, 'duration': 120},
    {'name': 'David', 'location': 'Sunset District', 'available_start': 750, 'available_end': 1125, 'duration': 45},
    {'name': 'Matthew', 'location': 'Alamo Square', 'available_start': 525, 'available_end': 825, 'duration': 90},
    {'name': 'Jessica', 'location': 'Financial District', 'available_start': 570, 'available_end': 1065, 'duration': 45},
    {'name': 'Melissa', 'location': 'North Beach', 'available_start': 435, 'available_end': 1005, 'duration': 45},
    {'name': 'Mark', 'location': 'Embarcadero', 'available_start': 915, 'available_end': 1020, 'duration': 45},
    {'name': 'Deborah', 'location': 'Presidio', 'available_start': 1260, 'available_end': 1305, 'duration': 45},
    {'name': 'Karen', 'location': 'Golden Gate Park', 'available_start': 1290, 'available_end': 1380, 'duration': 120},
    {'name': 'Laura', 'location': 'Bayview', 'available_start': 1335, 'available_end': 1365, 'duration': 15},
]

for friend in friends:
    friend['met'] = Bool(friend['name'])
    friend['start'] = Int(f'start_{friend["name"]}')
    friend['end'] = Int(f'end_{friend["name"]}')

travel_time = {
    ('Richmond District', 'Chinatown'): 20,
    ('Richmond District', 'Sunset District'): 11,
    ('Richmond District', 'Alamo Square'): 13,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'North Beach'): 17,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Richmond District', 'Bayview'): 27,
    ('Chinatown', 'Richmond District'): 20,
    ('Chinatown', 'Sunset District'): 29,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'Financial District'): 5,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', 'Embarcadero'): 5,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Bayview'): 20,
    ('Sunset District', 'Richmond District'): 12,
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'North Beach'): 28,
    ('Sunset District', 'Embarcadero'): 30,
    ('Sunset District', 'Presidio'): 16,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'Bayview'): 22,
    ('Alamo Square', 'Richmond District'): 11,
    ('Alamo Square', 'Chinatown'): 15,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Embarcadero'): 16,
    ('Alamo Square', 'Presidio'): 17,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Bayview'): 16,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'Chinatown'): 5,
    ('Financial District', 'Sunset District'): 30,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'North Beach'): 7,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Bayview'): 19,
    ('North Beach', 'Richmond District'): 18,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Sunset District'): 27,
    ('North Beach', 'Alamo Square'): 16,
    ('North Beach', 'Financial District'): 8,
    ('North Beach', 'Embarcadero'): 6,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Bayview'): 25,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Chinatown'): 7,
    ('Embarcadero', 'Sunset District'): 30,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'North Beach'): 5,
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Bayview'): 21,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'Sunset District'): 15,
    ('Presidio', 'Alamo Square'): 19,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Bayview'): 31,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Alamo Square'): 9,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'North Beach'): 23,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Bayview', 'Richmond District'): 25,
    ('Bayview', 'Chinatown'): 19,
    ('Bayview', 'Sunset District'): 23,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'Financial District'): 19,
    ('Bayview', 'North Beach'): 22,
    ('Bayview', 'Embarcadero'): 19,
    ('Bayview', 'Presidio'): 32,
    ('Bayview', 'Golden Gate Park'): 22,
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