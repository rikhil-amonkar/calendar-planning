from z3 import *
from itertools import combinations

friends = [
    {'name': 'Start', 'location': 'Embarcadero', 'available_start': 540, 'available_end': 540, 'duration': 0},
    {'name': 'Stephanie', 'location': 'Financial District', 'available_start': 495, 'available_end': 690, 'duration': 90},
    {'name': 'John', 'location': 'Alamo Square', 'available_start': 615, 'available_end': 1245, 'duration': 30},
]

for friend in friends:
    friend['met'] = Bool(friend['name'])
    friend['start'] = Int(f'start_{friend["name"]}')
    friend['end'] = Int(f'end_{friend["name"]}')

travel_time = {
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Alamo Square'): 17,
    ('Alamo Square', 'Embarcadero'): 17,
    ('Alamo Square', 'Financial District'): 17,
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
    # Time window and duration constraints
    solver.add(Implies(met, start >= friend['available_start']))
    solver.add(Implies(met, end == start + friend['duration']))
    solver.add(Implies(met, end <= friend['available_end']))
    # Travel time from Start location constraint
    travel_from_start = travel_time.get((friends[0]['location'], friend['location']), 0)
    solver.add(Implies(met, start >= 540 + travel_from_start))

# Add pairwise constraints between all friends (including Start)
for a, b in combinations(friends, 2):
    travel_ab = travel_time.get((a['location'], b['location']), None)
    travel_ba = travel_time.get((b['location'], a['location']), None)
    if not travel_ab or not travel_ba:
        continue
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