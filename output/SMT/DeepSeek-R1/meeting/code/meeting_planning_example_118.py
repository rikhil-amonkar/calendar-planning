from z3 import *

friends = [
    {'name': 'Start', 'location': 'Bayview', 'available_start': 540, 'available_end': 540, 'duration': 0},
    {'name': 'Richard', 'location': 'Union Square', 'available_start': 525, 'available_end': 780, 'duration': 120},
    {'name': 'Charles', 'location': 'Presidio', 'available_start': 585, 'available_end': 780, 'duration': 120},
]

for friend in friends:
    friend['met'] = Bool(friend['name'])
    friend['start'] = Int(f'start_{friend["name"]}')
    friend['end'] = Int(f'end_{friend["name"]}')

travel_time = {
    ('Bayview', 'Union Square'): 17,
    ('Bayview', 'Presidio'): 31,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'Presidio'): 24,
    ('Presidio', 'Bayview'): 31,
    ('Presidio', 'Union Square'): 22,
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

# Add travel constraints between locations
for i in range(1, len(friends)):
    for j in range(1, len(friends)):
        if i == j: continue
        a = friends[i]
        b = friends[j]
        travel = travel_time.get((a['location'], b['location']), None)
        if travel is None: continue
        # Either a comes before b or vice versa
        solver.add(Implies(And(a['met'], b['met']), 
                         Or(b['start'] >= a['end'] + travel,
                            a['start'] >= b['end'] + travel_time[(b['location'], a['location'])])
                         ))

# Travel from Start to first meeting
for friend in friends[1:]:
    travel = travel_time.get(('Bayview', friend['location']), 0)
    solver.add(Implies(friend['met'], friend['start'] >= 540 + travel))

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