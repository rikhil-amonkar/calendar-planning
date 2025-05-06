from z3 import *

def time_to_min(h, m):
    return h * 60 + m

friends = {
    'Mary': {
        'available_start': time_to_min(20, 0),
        'available_end': time_to_min(21, 15),
        'duration': 75,
        'location': 'Embarcadero',
    },
    'Kenneth': {
        'available_start': time_to_min(11, 15),
        'available_end': time_to_min(19, 15),
        'duration': 30,
        'location': 'The Castro',
    },
    'Joseph': {
        'available_start': time_to_min(20, 0),
        'available_end': time_to_min(22, 0),
        'duration': 120,
        'location': 'Haight-Ashbury',
    },
    'Sarah': {
        'available_start': time_to_min(11, 45),
        'available_end': time_to_min(14, 30),
        'duration': 90,
        'location': 'Union Square',
    },
    'Thomas': {
        'available_start': time_to_min(19, 15),
        'available_end': time_to_min(19, 45),
        'duration': 15,
        'location': 'North Beach',
    },
    'Daniel': {
        'available_start': time_to_min(13, 45),
        'available_end': time_to_min(20, 30),
        'duration': 15,
        'location': 'Pacific Heights',
    },
    'Richard': {
        'available_start': time_to_min(8, 0),
        'available_end': time_to_min(18, 45),
        'duration': 30,
        'location': 'Chinatown',
    },
    'Mark': {
        'available_start': time_to_min(17, 30),
        'available_end': time_to_min(21, 30),
        'duration': 120,
        'location': 'Golden Gate Park',
    },
    'David': {
        'available_start': time_to_min(20, 0),
        'available_end': time_to_min(21, 0),
        'duration': 60,
        'location': 'Marina District',
    },
    'Karen': {
        'available_start': time_to_min(13, 15),
        'available_end': time_to_min(18, 30),
        'duration': 120,
        'location': 'Russian Hill',
    },
}

travel_time = {
    ('Nob Hill', 'Embarcadero'): 9,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'Chinatown'): 6,
    ('Nob Hill', 'Golden Gate Park'): 17,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'The Castro'): 25,
    ('Embarcadero', 'Haight-Ashbury'): 21,
    ('Embarcadero', 'Union Square'): 10,
    ('Embarcadero', 'North Beach'): 5,
    ('Embarcadero', 'Pacific Heights'): 11,
    ('Embarcadero', 'Chinatown'): 7,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Marina District'): 12,
    ('Embarcadero', 'Russian Hill'): 8,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Embarcadero'): 22,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'North Beach'): 20,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Chinatown'): 22,
    ('The Castro', 'Golden Gate Park'): 11,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'Russian Hill'): 18,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'Embarcadero'): 20,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Haight-Ashbury', 'Union Square'): 19,
    ('Haight-Ashbury', 'North Beach'): 19,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Chinatown'): 19,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Embarcadero'): 11,
    ('Union Square', 'The Castro'): 17,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Pacific Heights'): 15,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Russian Hill'): 13,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Embarcadero'): 6,
    ('North Beach', 'The Castro'): 23,
    ('North Beach', 'Haight-Ashbury'): 18,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Pacific Heights'): 8,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Marina District'): 9,
    ('North Beach', 'Russian Hill'): 4,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Embarcadero'): 10,
    ('Pacific Heights', 'The Castro'): 16,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'North Beach'): 9,
    ('Pacific Heights', 'Chinatown'): 11,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'Marina District'): 6,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Chinatown', 'Nob Hill'): 9,
    ('Chinatown', 'Embarcadero'): 5,
    ('Chinatown', 'The Castro'): 22,
    ('Chinatown', 'Haight-Ashbury'): 19,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', 'Pacific Heights'): 10,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Marina District'): 12,
    ('Chinatown', 'Russian Hill'): 7,
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'North Beach'): 23,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Embarcadero'): 14,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'North Beach'): 11,
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'Chinatown'): 15,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Marina District', 'Russian Hill'): 8,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Union Square'): 10,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'Marina District'): 7,
}

s = Solver()

met = {name: Bool(f'met_{name}') for name in friends}
start = {name: Int(f'start_{name}') for name in friends}
end = {name: Int(f'end_{name}') for name in friends}

arrival_time = time_to_min(9, 0)  # 9:00 AM at Nob Hill

for name in friends:
    data = friends[name]
    loc = data['location']
    travel_from_nob_hill = travel_time.get(('Nob Hill', loc), 0)
    s.add(Implies(met[name], start[name] >= arrival_time + travel_from_nob_hill))
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