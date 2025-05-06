from z3 import *

def time_to_min(h, m):
    return h * 60 + m

friends = {
    'Jessica': {
        'available_start': time_to_min(16, 45),
        'available_end': time_to_min(19, 0),
        'duration': 30,
        'location': 'Embarcadero',
    },
    'Sandra': {
        'available_start': time_to_min(18, 30),
        'available_end': time_to_min(21, 45),
        'duration': 120,
        'location': 'Richmond District',
    },
    'Jason': {
        'available_start': time_to_min(16, 0),
        'available_end': time_to_min(16, 45),
        'duration': 30,
        'location': "Fisherman's Wharf",
    },
}

travel_time = {
    ('Bayview', 'Embarcadero'): 19,
    ('Bayview', 'Richmond District'): 25,
    ('Bayview', "Fisherman's Wharf"): 25,
    ('Embarcadero', 'Bayview'): 21,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', "Fisherman's Wharf"): 6,
    ('Richmond District', 'Bayview'): 26,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', "Fisherman's Wharf"): 18,
    ("Fisherman's Wharf", 'Bayview'): 26,
    ("Fisherman's Wharf", 'Embarcadero'): 8,
    ("Fisherman's Wharf", 'Richmond District'): 18,
}

s = Solver()

met = {name: Bool(f'met_{name}') for name in friends}
start = {name: Int(f'start_{name}') for name in friends}
end = {name: Int(f'end_{name}') for name in friends}

arrival_time = time_to_min(9, 0)  # 9:00 AM

# Initial location is Bayview
current_location = 'Bayview'

for name in friends:
    data = friends[name]
    loc = data['location']
    travel_from_current = travel_time.get((current_location, loc), 0)
    s.add(Implies(met[name], start[name] >= arrival_time + travel_from_current))
    s.add(Implies(met[name], start[name] >= data['available_start']))
    s.add(Implies(met[name], end[name] <= data['available_end']))
    s.add(Implies(met[name], end[name] == start[name] + data['duration']))

friend_names = list(friends.keys())
for i in range(len(friend_names)):
    for j in range(i + 1, len(friend_names)):
        X, Y = friend_names[i], friend_names[j]
        X_loc = friends[X]['location']
        Y_loc = friends[Y]['location']
        time_X_to_Y = travel_time.get((X_loc, Y_loc), 0)
        time_Y_to_X = travel_time.get((Y_loc, X_loc), 0)
        s.add(Or(
            Not(And(met[X], met[Y])),
            And(met[X], met[Y], end[X] + time_X_to_Y <= start[Y]),
            And(met[X], met[Y], end[Y] + time_Y_to_X <= start[X])
        ))

opt = Optimize()
opt.add(s.assertions())
opt.maximize(Sum([If(met[name], 1, 0) for name in friends]))

if opt.check() == sat:
    m = opt.model()
    total = sum(1 for name in friends if m.evaluate(met[name], model_completion=True))
    print(f"SOLUTION: Met {total} friends.")
    for name in friends:
        if m.evaluate(met[name], model_completion=True):
            s_min = m.evaluate(start[name], model_completion=True).as_long()
            e_min = m.evaluate(end[name], model_completion=True).as_long()
            s_h, s_m = divmod(s_min, 60)
            e_h, e_m = divmod(e_min, 60)
            print(f"{name}: {s_h:02}:{s_m:02} to {e_h:02}:{e_m:02}")
else:
    print("No solution found.")