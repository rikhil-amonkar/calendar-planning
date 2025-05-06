from z3 import *

def time_to_min(h, m):
    return h * 60 + m

friends = {
    'Emily': {
        'available_start': time_to_min(12, 15),  # 735 minutes (12:15 PM)
        'available_end': time_to_min(14, 15),    # 855 minutes (2:15 PM)
        'duration': 105,
        'location': 'Russian Hill',
    },
    'Mark': {
        'available_start': time_to_min(14, 45),  # 885 minutes (2:45 PM)
        'available_end': time_to_min(19, 30),     # 1170 minutes (7:30 PM)
        'duration': 60,
        'location': 'Presidio',
    },
    'Deborah': {
        'available_start': time_to_min(7, 30),    # 450 minutes (7:30 AM)
        'available_end': time_to_min(15, 30),     # 930 minutes (3:30 PM)
        'duration': 45,
        'location': 'Chinatown',
    },
    'Margaret': {
        'available_start': time_to_min(21, 30),   # 1290 minutes (9:30 PM)
        'available_end': time_to_min(22, 30),     # 1350 minutes (10:30 PM)
        'duration': 60,
        'location': 'Sunset District',
    },
    'George': {
        'available_start': time_to_min(7, 30),    # 450 minutes (7:30 AM)
        'available_end': time_to_min(14, 15),     # 855 minutes (2:15 PM)
        'duration': 60,
        'location': 'The Castro',
    },
    'Andrew': {
        'available_start': time_to_min(20, 15),   # 1215 minutes (8:15 PM)
        'available_end': time_to_min(22, 0),      # 1320 minutes (10:00 PM)
        'duration': 75,
        'location': 'Embarcadero',
    },
    'Steven': {
        'available_start': time_to_min(11, 15),    # 675 minutes (11:15 AM)
        'available_end': time_to_min(21, 15),      # 1275 minutes (9:15 PM)
        'duration': 105,
        'location': 'Golden Gate Park',
    },
}

travel_time = {
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'Presidio'): 18,
    ('Alamo Square', 'Chinatown'): 16,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Embarcadero'): 17,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Presidio', 'Alamo Square'): 18,
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'Sunset District'): 15,
    ('Presidio', 'The Castro'): 21,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'Russian Hill'): 7,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Sunset District'): 29,
    ('Chinatown', 'The Castro'): 22,
    ('Chinatown', 'Embarcadero'): 5,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Presidio'): 16,
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Embarcadero'): 31,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Presidio'): 20,
    ('The Castro', 'Chinatown'): 20,
    ('The Castro', 'Sunset District'): 17,
    ('The Castro', 'Embarcadero'): 22,
    ('The Castro', 'Golden Gate Park'): 11,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Embarcadero', 'Russian Hill'): 8,
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Chinatown'): 7,
    ('Embarcadero', 'Sunset District'): 30,
    ('Embarcadero', 'The Castro'): 25,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Golden Gate Park', 'Alamo Square'): 10,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Embarcadero'): 25,
}

s = Solver()

met = {name: Bool(f'met_{name}') for name in friends}
start = {name: Int(f'start_{name}') for name in friends}
end = {name: Int(f'end_{name}') for name in friends}

arrival_time = time_to_min(9, 0)  # 9:00 AM at Alamo Square

for name in friends:
    data = friends[name]
    loc = data['location']
    s.add(Implies(met[name], start[name] >= data['available_start']))
    s.add(Implies(met[name], end[name] <= data['available_end']))
    s.add(Implies(met[name], end[name] == start[name] + data['duration']))
    
    # Initial travel from Alamo Square to this friend's location
    initial_travel = travel_time.get(('Alamo Square', loc), 0)
    clauses = [start[name] >= arrival_time + initial_travel]
    
    # Travel from other friends' locations to this friend
    for other in friends:
        if other == name:
            continue
        other_loc = friends[other]['location']
        travel = travel_time.get((other_loc, loc), 0)
        clauses.append(And(met[other], start[name] >= end[other] + travel))
    
    s.add(Implies(met[name], Or(clauses)))

# Ensure no overlapping meetings considering travel time between any two friends
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
opt.maximize(Sum([If(met[name], 1, 0) for name in friends))

if opt.check() == sat:
    m = opt.model()
    total = sum(1 for name in friends if m.evaluate(met[name]))
    print(f"SOLUTION: Met {total} friends.")
    schedule = []
    for name in friends:
        if m.evaluate(met[name]):
            s_min = m.evaluate(start[name]).as_long()
            e_min = m.evaluate(end[name]).as_long()
            s_h, s_m = divmod(s_min, 60)
            e_h, e_m = divmod(e_min, 60)
            schedule.append((s_min, name, s_h, s_m, e_h, e_m))
    schedule.sort()
    for entry in schedule:
        _, name, s_h, s_m, e_h, e_m = entry
        print(f"{name}: {s_h:02}:{s_m:02} to {e_h:02}:{e_m:02}")
else:
    print("No solution found.")