from z3 import *
from itertools import combinations

friends = [
    {'name': 'Start', 'location': 'Golden Gate Park', 'available_start': 540, 'available_end': 540, 'duration': 0},
    {'name': 'Sarah', 'location': 'Haight-Ashbury', 'available_start': 1020, 'available_end': 1290, 'duration': 105},
    {'name': 'Patricia', 'location': 'Sunset District', 'available_start': 1020, 'available_end': 1185, 'duration': 45},
    {'name': 'Matthew', 'location': 'Marina District', 'available_start': 555, 'available_end': 720, 'duration': 15},
    {'name': 'Joseph', 'location': 'Financial District', 'available_start': 855, 'available_end': 1125, 'duration': 30},
    {'name': 'Robert', 'location': 'Union Square', 'available_start': 615, 'available_end': 1305, 'duration': 15},
]

for friend in friends:
    friend['met'] = Bool(friend['name'])
    friend['start'] = Int(f'start_{friend["name"]}')
    friend['end'] = Int(f'end_{friend["name"]}')

travel_time = {
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Haight-Ashbury', 'Union Square'): 17,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'Union Square'): 30,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Union Square'): 16,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Financial District', 'Sunset District'): 31,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Union Square'): 9,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'Sunset District'): 26,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Financial District'): 9,
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
    travel_ab = travel_time.get((a['location'], b['location']), None)
    travel_ba = travel_time.get((b['location'], a['location']), None)
    if travel_ab is None or travel_ba is None:
        continue
    # Ensure travel time is respected in either order
    solver.add(Implies(And(a['met'], b['met']),
                  Or(b['start'] >= a['end'] + travel_ab,
                     a['start'] >= b['end'] + travel_ba)))

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