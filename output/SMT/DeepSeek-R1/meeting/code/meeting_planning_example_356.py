from z3 import *

def time_to_min(h, m):
    return h * 60 + m

friends = {
    'Barbara': {
        'available_start': time_to_min(13, 45),
        'available_end': time_to_min(20, 15),
        'duration': 60,
        'location': 'North Beach',
    },
    'Margaret': {
        'available_start': time_to_min(10, 15),
        'available_end': time_to_min(15, 15),
        'duration': 30,
        'location': 'Presidio',
    },
    'Kevin': {
        'available_start': time_to_min(20, 0),
        'available_end': time_to_min(20, 45),
        'duration': 30,
        'location': 'Haight-Ashbury',
    },
    'Kimberly': {
        'available_start': time_to_min(7, 45),
        'available_end': time_to_min(16, 45),
        'duration': 30,
        'location': 'Union Square',
    },
}

travel_time = {
    ('Bayview', 'North Beach'): 21,
    ('Bayview', 'Presidio'): 31,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Union Square'): 17,
    ('North Beach', 'Bayview'): 22,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Haight-Ashbury'): 18,
    ('North Beach', 'Union Square'): 7,
    ('Presidio', 'Bayview'): 31,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Presidio', 'Union Square'): 22,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'North Beach'): 19,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Union Square'): 17,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Haight-Ashbury'): 18,
}

s = Solver()

met = {name: Bool(f'met_{name}') for name in friends}
start = {name: Int(f'start_{name}') for name in friends}
end = {name: Int(f'end_{name}') for name in friends}

arrival_time = time_to_min(9, 0)  # 9:00 AM at Bayview

for name in friends:
    data = friends[name]
    loc = data['location']
    travel = travel_time.get(('Bayview', loc), 0)
    s.add(Implies(met[name], start[name] >= arrival_time + travel))
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
    schedule = []
    for name in friends:
        if m.evaluate(met[name], model_completion=True):
            s_min = m.evaluate(start[name], model_completion=True).as_long()
            e_min = m.evaluate(end[name], model_completion=True).as_long()
            s_h, s_m = divmod(s_min, 60)
            e_h, e_m = divmod(e_min, 60)
            schedule.append((s_min, name, s_h, s_m, e_h, e_m))
    schedule.sort()
    for entry in schedule:
        _, name, s_h, s_m, e_h, e_m = entry
        print(f"{name}: {s_h:02}:{s_m:02} to {e_h:02}:{e_m:02}")
else:
    print("No solution found.")