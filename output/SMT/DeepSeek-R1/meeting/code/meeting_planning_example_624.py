from z3 import *

def time_to_min(h, m):
    return h * 60 + m

friends = {
    'Carol': {
        'available_start': time_to_min(21, 30),
        'available_end': time_to_min(22, 30),
        'duration': 60,
        'location': 'Haight-Ashbury',
    },
    'Laura': {
        'available_start': time_to_min(11, 45),
        'available_end': time_to_min(21, 30),
        'duration': 60,
        'location': "Fisherman's Wharf",
    },
    'Karen': {
        'available_start': time_to_min(7, 15),
        'available_end': time_to_min(14, 0),
        'duration': 75,
        'location': 'The Castro',
    },
    'Elizabeth': {
        'available_start': time_to_min(12, 15),
        'available_end': time_to_min(21, 30),
        'duration': 75,
        'location': 'Chinatown',
    },
    'Deborah': {
        'available_start': time_to_min(12, 0),
        'available_end': time_to_min(15, 0),
        'duration': 105,
        'location': 'Alamo Square',
    },
    'Jason': {
        'available_start': time_to_min(14, 45),
        'available_end': time_to_min(19, 0),
        'duration': 90,
        'location': 'North Beach',
    },
    'Steven': {
        'available_start': time_to_min(14, 45),
        'available_end': time_to_min(18, 30),
        'duration': 120,
        'location': 'Russian Hill',
    },
}

travel_time = {
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', "Fisherman's Wharf"): 24,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Alamo Square'): 10,
    ('Golden Gate Park', 'North Beach'): 24,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', "Fisherman's Wharf"): 23,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Haight-Ashbury', 'Chinatown'): 19,
    ('Haight-Ashbury', 'Alamo Square'): 5,
    ('Haight-Ashbury', 'North Beach'): 19,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ("Fisherman's Wharf", 'Golden Gate Park'): 25,
    ("Fisherman's Wharf", 'Haight-Ashbury'): 22,
    ("Fisherman's Wharf", 'The Castro'): 26,
    ("Fisherman's Wharf", 'Chinatown'): 12,
    ("Fisherman's Wharf", 'Alamo Square'): 20,
    ("Fisherman's Wharf", 'North Beach'): 6,
    ("Fisherman's Wharf", 'Russian Hill'): 7,
    ('The Castro', 'Golden Gate Park'): 11,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('The Castro', "Fisherman's Wharf"): 24,
    ('The Castro', 'Chinatown'): 20,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'North Beach'): 20,
    ('The Castro', 'Russian Hill'): 18,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Haight-Ashbury'): 19,
    ('Chinatown', "Fisherman's Wharf"): 8,
    ('Chinatown', 'The Castro'): 22,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', 'Russian Hill'): 7,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Haight-Ashbury'): 5,
    ('Alamo Square', "Fisherman's Wharf"): 19,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Chinatown'): 16,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Russian Hill'): 13,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Haight-Ashbury'): 18,
    ('North Beach', "Fisherman's Wharf"): 5,
    ('North Beach', 'The Castro'): 22,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Alamo Square'): 16,
    ('North Beach', 'Russian Hill'): 4,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', "Fisherman's Wharf"): 7,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'North Beach'): 5,
}

s = Solver()

met = {name: Bool(f'met_{name}') for name in friends}
start = {name: Int(f'start_{name}') for name in friends}
end = {name: Int(f'end_{name}') for name in friends}

arrival_time = time_to_min(9, 0)  # 9:00 AM

for name in friends:
    data = friends[name]
    loc = data['location']
    travel_from_ggp = travel_time.get(('Golden Gate Park', loc), 0)
    s.add(Implies(met[name], start[name] >= arrival_time + travel_from_ggp))
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