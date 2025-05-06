from z3 import *

def time_to_min(h, m):
    return h * 60 + m

friends = {
    'Sarah': {
        'available_start': time_to_min(10, 45),
        'available_end': time_to_min(19, 0),
        'duration': 30,
        'location': "Sunset District",
    },
    'Richard': {
        'available_start': time_to_min(11, 45),
        'available_end': time_to_min(15, 45),
        'duration': 90,
        'location': "Haight-Ashbury",
    },
    'Elizabeth': {
        'available_start': time_to_min(11, 0),
        'available_end': time_to_min(17, 15),
        'duration': 120,
        'location': "Mission District",
    },
    'Michelle': {
        'available_start': time_to_min(18, 15),
        'available_end': time_to_min(20, 45),
        'duration': 90,
        'location': "Golden Gate Park",
    },
}

travel_time = {
    ('Richmond District', 'Sunset District'): 11,
    ('Richmond District', 'Haight-Ashbury'): 10,
    ('Richmond District', 'Mission District'): 20,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Sunset District', 'Richmond District'): 12,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Mission District'): 24,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Haight-Ashbury', 'Richmond District'): 10,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Mission District', 'Richmond District'): 20,
    ('Mission District', 'Sunset District'): 24,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Mission District'): 17,
}

s = Solver()

met = {}
start = {}
end = {}
for name in friends:
    met[name] = Bool(f'met_{name}')
    start[name] = Int(f'start_{name}')
    end[name] = Int(f'end_{name}')

arrival_time = time_to_min(9, 0)  # 9:00 AM

for name in friends:
    data = friends[name]
    loc = data['location']
    travel_from_richmond = travel_time.get(('Richmond District', loc), 0)
    s.add(Implies(met[name], start[name] >= arrival_time + travel_from_richmond))
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