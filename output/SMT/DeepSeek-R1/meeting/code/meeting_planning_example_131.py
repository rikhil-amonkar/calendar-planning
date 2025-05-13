from z3 import *
from itertools import combinations

friends = [
    {'name': 'Start', 'location': 'Pacific Heights', 'available_start': 540, 'available_end': 540, 'duration': 0},
    {'name': 'Jason', 'location': 'Presidio', 'available_start': 600, 'available_end': 975, 'duration': 90},
    {'name': 'Kenneth', 'location': 'Marina District', 'available_start': 930, 'available_end': 1005, 'duration': 45},
]

for friend in friends:
    friend['met'] = Bool(friend['name'])
    friend['start'] = Int(f'start_{friend["name"]}')
    friend['end'] = Int(f'end_{friend["name"]}')

travel_time = {
    ('Pacific Heights', 'Presidio'): 11,
    ('Pacific Heights', 'Marina District'): 6,
    ('Presidio', 'Pacific Heights'): 11,
    ('Presidio', 'Marina District'): 10,
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'Presidio'): 10,
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
    # Add travel time from Start location
    travel_from_start = travel_time.get((friends[0]['location'], friend['location']), 0)
    solver.add(Implies(met, start >= 540 + travel_from_start))

# Add pairwise constraints between all friends (including Start)
for a, b in combinations(friends, 2):
    travel_ab = travel_time.get((a['location'], b['location']), None)
    travel_ba = travel_time.get((b['location'], a['location']), None)
    if travel_ab is None or travel_ba is None:
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