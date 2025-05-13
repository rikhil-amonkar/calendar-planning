from z3 import *
from itertools import combinations

friends = [
    {'name': 'Start', 'location': 'Chinatown', 'available_start': 540, 'available_end': 540, 'duration': 0},
    {'name': 'Richard', 'location': 'Embarcadero', 'available_start': 915, 'available_end': 1125, 'duration': 90},
    {'name': 'Mark', 'location': 'Pacific Heights', 'available_start': 900, 'available_end': 1020, 'duration': 45},
    {'name': 'Matthew', 'location': 'Russian Hill', 'available_start': 1050, 'available_end': 1260, 'duration': 90},
    {'name': 'Rebecca', 'location': 'Haight-Ashbury', 'available_start': 885, 'available_end': 1080, 'duration': 60},
    {'name': 'Melissa', 'location': 'Golden Gate Park', 'available_start': 825, 'available_end': 1050, 'duration': 90},
    {'name': 'Margaret', 'location': "Fisherman's Wharf", 'available_start': 885, 'available_end': 1230, 'duration': 15},
    {'name': 'Emily', 'location': 'Sunset District', 'available_start': 945, 'available_end': 1020, 'duration': 45},
    {'name': 'George', 'location': 'The Castro', 'available_start': 840, 'available_end': 975, 'duration': 75},
]

for friend in friends:
    friend['met'] = Bool(friend['name'])
    friend['start'] = Int(f'start_{friend["name"]}')
    friend['end'] = Int(f'end_{friend["name"]}')

travel_time = {
    ('Chinatown', 'Embarcadero'): 5,
    ('Chinatown', 'Pacific Heights'): 10,
    ('Chinatown', 'Russian Hill'): 7,
    ('Chinatown', 'Haight-Ashbury'): 19,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', "Fisherman's Wharf"): 8,
    ('Chinatown', 'Sunset District'): 29,
    ('Chinatown', 'The Castro'): 22,
    ('Embarcadero', 'Chinatown'): 7,
    ('Embarcadero', 'Pacific Heights'): 11,
    ('Embarcadero', 'Russian Hill'): 8,
    ('Embarcadero', 'Haight-Ashbury'): 21,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', "Fisherman's Wharf"): 6,
    ('Embarcadero', 'Sunset District'): 30,
    ('Embarcadero', 'The Castro'): 25,
    ('Pacific Heights', 'Chinatown'): 11,
    ('Pacific Heights', 'Embarcadero'): 10,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', "Fisherman's Wharf"): 13,
    ('Pacific Heights', 'Sunset District'): 21,
    ('Pacific Heights', 'The Castro'): 16,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', "Fisherman's Wharf"): 7,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'The Castro'): 21,
    ('Haight-Ashbury', 'Chinatown'): 19,
    ('Haight-Ashbury', 'Embarcadero'): 20,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', "Fisherman's Wharf"): 23,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', "Fisherman's Wharf"): 24,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'The Castro'): 13,
    ("Fisherman's Wharf", 'Chinatown'): 12,
    ("Fisherman's Wharf", 'Embarcadero'): 8,
    ("Fisherman's Wharf", 'Pacific Heights'): 12,
    ("Fisherman's Wharf", 'Russian Hill'): 7,
    ("Fisherman's Wharf", 'Haight-Ashbury'): 22,
    ("Fisherman's Wharf", 'Golden Gate Park'): 25,
    ("Fisherman's Wharf", 'Sunset District'): 27,
    ("Fisherman's Wharf", 'The Castro'): 27,
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'Embarcadero'): 30,
    ('Sunset District', 'Pacific Heights'): 21,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', "Fisherman's Wharf"): 29,
    ('Sunset District', 'The Castro'): 17,
    ('The Castro', 'Chinatown'): 22,
    ('The Castro', 'Embarcadero'): 22,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('The Castro', 'Golden Gate Park'): 11,
    ('The Castro', "Fisherman's Wharf"): 24,
    ('The Castro', 'Sunset District'): 17,
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

# Meeting order constraints including travel times
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