from z3 import *

def time_to_min(h, m):
    return h * 60 + m

friends = {
    'Elizabeth': {
        'available_start': time_to_min(19, 0),
        'available_end': time_to_min(20, 45),
        'duration': 105,
        'location': 'Marina District',
    },
    'Joshua': {
        'available_start': time_to_min(8, 30),
        'available_end': time_to_min(13, 15),
        'duration': 105,
        'location': 'Presidio',
    },
    'Timothy': {
        'available_start': time_to_min(19, 45),
        'available_end': time_to_min(22, 0),
        'duration': 90,
        'location': 'North Beach',
    },
    'David': {
        'available_start': time_to_min(10, 45),
        'available_end': time_to_min(12, 30),
        'duration': 30,
        'location': 'Embarcadero',
    },
    'Kimberly': {
        'available_start': time_to_min(16, 45),
        'available_end': time_to_min(21, 30),
        'duration': 75,
        'location': 'Haight-Ashbury',
    },
    'Lisa': {
        'available_start': time_to_min(17, 30),
        'available_end': time_to_min(21, 45),
        'duration': 45,
        'location': 'Golden Gate Park',
    },
    'Ronald': {
        'available_start': time_to_min(8, 0),
        'available_end': time_to_min(9, 30),
        'duration': 90,
        'location': 'Richmond District',
    },
    'Stephanie': {
        'available_start': time_to_min(15, 30),
        'available_end': time_to_min(16, 30),
        'duration': 30,
        'location': 'Alamo Square',
    },
    'Helen': {
        'available_start': time_to_min(17, 30),
        'available_end': time_to_min(18, 30),
        'duration': 45,
        'location': 'Financial District',
    },
    'Laura': {
        'available_start': time_to_min(17, 45),
        'available_end': time_to_min(21, 15),
        'duration': 90,
        'location': 'Sunset District',
    },
}

travel_time = {
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'Presidio'): 20,
    ('The Castro', 'North Beach'): 20,
    ('The Castro', 'Embarcadero'): 22,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('The Castro', 'Golden Gate Park'): 11,
    ('The Castro', 'Richmond District'): 16,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Financial District'): 21,
    ('The Castro', 'Sunset District'): 17,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'North Beach'): 11,
    ('Marina District', 'Embarcadero'): 14,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Sunset District'): 19,
    ('Presidio', 'The Castro'): 21,
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Alamo Square'): 19,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'Sunset District'): 15,
    ('North Beach', 'The Castro'): 23,
    ('North Beach', 'Marina District'): 9,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Embarcadero'): 6,
    ('North Beach', 'Haight-Ashbury'): 18,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Richmond District'): 18,
    ('North Beach', 'Alamo Square'): 16,
    ('North Beach', 'Financial District'): 8,
    ('North Beach', 'Sunset District'): 27,
    ('Embarcadero', 'The Castro'): 25,
    ('Embarcadero', 'Marina District'): 12,
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'North Beach'): 5,
    ('Embarcadero', 'Haight-Ashbury'): 21,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'Sunset District'): 30,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'North Beach'): 19,
    ('Haight-Ashbury', 'Embarcadero'): 20,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'Richmond District'): 10,
    ('Haight-Ashbury', 'Alamo Square'): 5,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'North Beach'): 23,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'Alamo Square'): 9,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Richmond District', 'The Castro'): 16,
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'North Beach'): 17,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Haight-Ashbury'): 10,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Richmond District', 'Alamo Square'): 13,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'Sunset District'): 11,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Marina District'): 15,
    ('Alamo Square', 'Presidio'): 17,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Embarcadero'): 16,
    ('Alamo Square', 'Haight-Ashbury'): 5,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Richmond District'): 11,
    ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'Sunset District'): 16,
    ('Financial District', 'The Castro'): 20,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'North Beach'): 7,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Sunset District'): 30,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Presidio'): 16,
    ('Sunset District', 'North Beach'): 28,
    ('Sunset District', 'Embarcadero'): 30,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'Richmond District'): 12,
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Financial District'): 30,
}

s = Solver()

met = {name: Bool(f'met_{name}') for name in friends}
start = {name: Int(f'start_{name}') for name in friends}
end = {name: Int(f'end_{name}') for name in friends}

arrival_time = time_to_min(9, 0)  # 9:00 AM at The Castro

for name in friends:
    data = friends[name]
    loc = data['location']
    initial_travel = travel_time[('The Castro', loc)] if ('The Castro', loc) in travel_time else 0
    
    # Basic constraints for availability and duration
    s.add(Implies(met[name], start[name] >= data['available_start']))
    s.add(Implies(met[name], end[name] == start[name] + data['duration']))
    s.add(Implies(met[name], end[name] <= data['available_end']))
    
    # Start time must be >= arrival + initial travel OR after another friend's end + travel
    constraints = [start[name] >= arrival_time + initial_travel]
    for other in friends:
        if other != name:
            other_loc = friends[other]['location']
            if (other_loc, loc) in travel_time:
                travel = travel_time[(other_loc, loc)]
                constraints.append(And(met[other], start[name] >= end[other] + travel))
    s.add(Implies(met[name], Or(constraints)))

# Pairwise constraints for all friends
friend_names = list(friends.keys())
for i in range(len(friend_names)):
    for j in range(i + 1, len(friend_names)):
        a = friend_names[i]
        b = friend_names[j]
        a_loc = friends[a]['location']
        b_loc = friends[b]['location']
        time_ab = travel_time[(a_loc, b_loc)] if (a_loc, b_loc) in travel_time else 0
        time_ba = travel_time[(b_loc, a_loc)] if (b_loc, a_loc) in travel_time else 0
        
        s.add(Implies(And(met[a], met[b]), Or(
            end[a] + time_ab <= start[b],
            end[b] + time_ba <= start[a]
        )))

# Optimize to maximize friends met
opt = Optimize()
opt.add(s.assertions())
opt.maximize(Sum([If(met[name], 1, 0) for name in friends]))

if opt.check() == sat:
    m = opt.model()
    total = sum(1 for name in friends if m.evaluate(met[name]))
    print(f"SOLUTION: Met {total} friends.")
    schedule = []
    for name in friends:
        if m.evaluate(met[name]):
            s_val = m.evaluate(start[name]).as_long()
            e_val = m.evaluate(end[name]).as_long()
            s_h, s_m = divmod(s_val, 60)
            e_h, e_m = divmod(e_val, 60)
            schedule.append((s_val, name, s_h, s_m, e_h, e_m))
    schedule.sort()
    for entry in schedule:
        _, name, sh, sm, eh, em = entry
        print(f"{name}: {sh:02}:{sm:02} to {eh:02}:{em:02}")
else:
    print("No solution found.")