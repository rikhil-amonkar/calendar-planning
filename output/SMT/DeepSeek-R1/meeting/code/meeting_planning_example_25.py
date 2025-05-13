from z3 import *

friends = [
    {'name': 'Start', 'location': 'Golden Gate Park', 'available_start': 540, 'available_end': 540, 'duration': 0},
    {'name': 'David', 'location': 'Chinatown', 'available_start': 960, 'available_end': 1290, 'duration': 105},
]

for friend in friends:
    friend['met'] = Bool(friend['name'])
    friend['start'] = Int(f'start_{friend["name"]}')
    friend['end'] = Int(f'end_{friend["name"]}')

travel_time = {
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Chinatown', 'Golden Gate Park'): 23,
}

solver = Solver()

# Start must be met with fixed times
solver.add(friends[0]['met'] == True)
solver.add(friends[0]['start'] == 540)
solver.add(friends[0]['end'] == 540)

# Constraints for David
david = friends[1]
solver.add(Implies(david['met'], david['start'] >= david['available_start']))
solver.add(Implies(david['met'], david['end'] == david['start'] + david['duration']))
solver.add(Implies(david['met'], david['end'] <= david['available_end']))

# Travel constraints between Start and David
solver.add(Implies(And(friends[0]['met'], david['met']), 
                  david['start'] >= friends[0]['end'] + travel_time[(friends[0]['location'], david['location'])]))

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
    print("Optimal Schedule:")
    for name, s, e in schedule:
        print(f"{name}: {s//60:02d}:{s%60:02d}-{e//60:02d}:{e%60:02d}")
else:
    print("No valid schedule found.")