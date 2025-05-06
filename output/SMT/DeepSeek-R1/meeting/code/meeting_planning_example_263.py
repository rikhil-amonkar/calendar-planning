from z3 import *

def time_to_min(h, m):
    return h * 60 + m

friends = {
    'Karen': {
        'available_start': time_to_min(8, 45),
        'available_end': time_to_min(15, 0),
        'duration': 30,
        'location': "Fisherman's Wharf",
    },
    'Anthony': {
        'available_start': time_to_min(9, 15),
        'available_end': time_to_min(21, 30),
        'duration': 105,
        'location': "Financial District",
    },
    'Betty': {
        'available_start': time_to_min(19, 45),
        'available_end': time_to_min(21, 45),
        'duration': 15,
        'location': "Embarcadero",
    },
}

travel_time = {
    ('Bayview', 'Embarcadero'): 19,
    ('Bayview', "Fisherman's Wharf"): 25,
    ('Bayview', "Financial District"): 19,
    ('Embarcadero', 'Bayview'): 21,
    ('Embarcadero', "Fisherman's Wharf"): 6,
    ('Embarcadero', "Financial District"): 5,
    ("Fisherman's Wharf", 'Bayview'): 26,
    ("Fisherman's Wharf", 'Embarcadero'): 8,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Financial District", 'Bayview'): 19,
    ("Financial District", 'Embarcadero'): 4,
    ("Financial District", "Fisherman's Wharf"): 10,
}

s = Solver()

met = {}
start = {}
end = {}
for name in friends:
    met[name] = Bool(f'met_{name}')
    start[name] = Int(f'start_{name}')
    end[name] = Int(f'end_{name}')

for name in friends:
    data = friends[name]
    loc = data['location']
    travel_from_bayview = travel_time.get(('Bayview', loc), 0)
    s.add(Implies(met[name], start[name] >= 540 + travel_from_bayview))
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