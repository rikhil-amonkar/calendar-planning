from z3 import *

def time_to_min(h, m):
    return h * 60 + m

friends = {
    'Stephanie': {
        'available_start': time_to_min(15, 30),
        'available_end': time_to_min(22, 0),
        'duration': 30,
        'location': "Fisherman's Wharf",
    },
    'Lisa': {
        'available_start': time_to_min(10, 45),
        'available_end': time_to_min(17, 15),
        'duration': 15,
        'location': 'Financial District',
    },
    'Melissa': {
        'available_start': time_to_min(17, 0),
        'available_end': time_to_min(21, 45),
        'duration': 120,
        'location': 'Russian Hill',
    },
    'Betty': {
        'available_start': time_to_min(10, 45),
        'available_end': time_to_min(14, 15),
        'duration': 60,
        'location': 'Marina District',
    },
    'Sarah': {
        'available_start': time_to_min(16, 15),
        'available_end': time_to_min(19, 30),
        'duration': 105,
        'location': 'Richmond District',
    },
    'Daniel': {
        'available_start': time_to_min(18, 30),
        'available_end': time_to_min(21, 45),
        'duration': 60,
        'location': 'Pacific Heights',
    },
    'Joshua': {
        'available_start': time_to_min(9, 0),
        'available_end': time_to_min(15, 30),
        'duration': 15,
        'location': 'Haight-Ashbury',
    },
    'Joseph': {
        'available_start': time_to_min(7, 0),
        'available_end': time_to_min(13, 0),
        'duration': 45,
        'location': 'Presidio',
    },
    'Andrew': {
        'available_start': time_to_min(19, 45),
        'available_end': time_to_min(22, 0),
        'duration': 105,
        'location': 'Nob Hill',
    },
    'John': {
        'available_start': time_to_min(13, 15),
        'available_end': time_to_min(19, 45),
        'duration': 45,
        'location': 'The Castro',
    },
}

travel_time = {
    ('Embarcadero', "Fisherman's Wharf"): 6,
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'Russian Hill'): 8,
    ('Embarcadero', 'Marina District'): 12,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Pacific Heights'): 11,
    ('Embarcadero', 'Haight-Ashbury'): 21,
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'The Castro'): 25,
    ("Fisherman's Wharf", 'Embarcadero'): 8,
    ("Fisherman's Wharf", 'Financial District'): 11,
    ("Fisherman's Wharf", 'Russian Hill'): 7,
    ("Fisherman's Wharf", 'Marina District'): 9,
    ("Fisherman's Wharf", 'Richmond District'): 18,
    ("Fisherman's Wharf", 'Pacific Heights'): 12,
    ("Fisherman's Wharf", 'Haight-Ashbury'): 22,
    ("Fisherman's Wharf", 'Presidio'): 17,
    ("Fisherman's Wharf", 'Nob Hill'): 11,
    ("Fisherman's Wharf", 'The Castro'): 27,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', "Fisherman's Wharf"): 10,
    ('Financial District', 'Russian Hill'): 11,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Nob Hill'): 8,
    ('Financial District', 'The Castro'): 20,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Russian Hill', "Fisherman's Wharf"): 7,
    ('Russian Hill', 'Financial District'): 11,
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'Richmond District'): 14,
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'The Castro'): 21,
    ('Marina District', 'Embarcadero'): 14,
    ('Marina District', "Fisherman's Wharf"): 10,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'The Castro'): 22,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', "Fisherman's Wharf"): 18,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'Russian Hill'): 13,
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'Pacific Heights'): 10,
    ('Richmond District', 'Haight-Ashbury'): 10,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Nob Hill'): 17,
    ('Richmond District', 'The Castro'): 16,
    ('Pacific Heights', 'Embarcadero'): 10,
    ('Pacific Heights', "Fisherman's Wharf"): 13,
    ('Pacific Heights', 'Financial District'): 13,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Pacific Heights', 'Marina District'): 6,
    ('Pacific Heights', 'Richmond District'): 12,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Pacific Heights', 'Presidio'): 11,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'The Castro'): 16,
    ('Haight-Ashbury', 'Embarcadero'): 20,
    ('Haight-Ashbury', "Fisherman's Wharf"): 23,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Richmond District'): 10,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', "Fisherman's Wharf"): 19,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Pacific Heights'): 11,
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'The Castro'): 21,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Nob Hill', "Fisherman's Wharf"): 10,
    ('Nob Hill', 'Financial District'): 9,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'Richmond District'): 14,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Nob Hill', 'Presidio'): 17,
    ('Nob Hill', 'The Castro'): 17,
    ('The Castro', 'Embarcadero'): 22,
    ('The Castro', "Fisherman's Wharf"): 24,
    ('The Castro', 'Financial District'): 21,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'Richmond District'): 16,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('The Castro', 'Presidio'): 20,
    ('The Castro', 'Nob Hill'): 16,
}

s = Solver()

met = {name: Bool(f'met_{name}') for name in friends}
start = {name: Int(f'start_{name}') for name in friends}
end = {name: Int(f'end_{name}') for name in friends}

arrival_time = time_to_min(9, 0)  # 9:00 AM

for name in friends:
    data = friends[name]
    loc = data['location']
    travel_from_embarcadero = travel_time.get(('Embarcadero', loc), 0)
    s.add(Implies(met[name], start[name] >= arrival_time + travel_from_embarcadero))
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