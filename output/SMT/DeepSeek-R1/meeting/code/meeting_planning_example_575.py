from z3 import *

def time_to_min(h, m):
    return h * 60 + m

friends = {
    'Rebecca': {
        'available_start': time_to_min(18, 15),
        'available_end': time_to_min(20, 45),
        'duration': 60,
        'location': 'Presidio',
    },
    'Linda': {
        'available_start': time_to_min(15, 30),
        'available_end': time_to_min(19, 45),
        'duration': 30,
        'location': 'Sunset District',
    },
    'Elizabeth': {
        'available_start': time_to_min(17, 15),
        'available_end': time_to_min(19, 30),
        'duration': 105,
        'location': 'Haight-Ashbury',
    },
    'William': {
        'available_start': time_to_min(13, 15),
        'available_end': time_to_min(19, 30),
        'duration': 30,
        'location': 'Mission District',
    },
    'Robert': {
        'available_start': time_to_min(14, 15),
        'available_end': time_to_min(21, 30),
        'duration': 45,
        'location': 'Golden Gate Park',
    },
    'Mark': {
        'available_start': time_to_min(10, 0),
        'available_end': time_to_min(21, 15),
        'duration': 75,
        'location': 'Russian Hill',
    },
}

travel_time = {
    ('The Castro', 'Presidio'): 20,
    ('The Castro', 'Sunset District'): 17,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('The Castro', 'Mission District'): 7,
    ('The Castro', 'Golden Gate Park'): 11,
    ('The Castro', 'Russian Hill'): 18,
    ('Presidio', 'The Castro'): 21,
    ('Presidio', 'Sunset District'): 15,
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Presidio', 'Mission District'): 26,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Russian Hill'): 14,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Presidio'): 16,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Mission District'): 24,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'Russian Hill'): 24,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Mission District', 'The Castro'): 7,
    ('Mission District', 'Presidio'): 25,
    ('Mission District', 'Sunset District'): 24,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Mission District', 'Russian Hill'): 15,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Mission District'): 16,
    ('Russian Hill', 'Golden Gate Park'): 21,
}

s = Solver()

met = {name: Bool(f'met_{name}') for name in friends}
start = {name: Int(f'start_{name}') for name in friends}
end = {name: Int(f'end_{name}') for name in friends}

arrival_time = time_to_min(9, 0)  # 9:00 AM at The Castro

for name in friends:
    data = friends[name]
    loc = data['location']
    # Travel time from The Castro to friend's location
    travel = travel_time.get(('The Castro', loc), 0)
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