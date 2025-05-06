from z3 import *

def time_to_min(h, m):
    return h * 60 + m

friends = {
    'Charles': {
        'available_start': time_to_min(18, 0),
        'available_end': time_to_min(20, 45),
        'duration': 90,
        'location': 'Alamo Square',
    },
    'Margaret': {
        'available_start': time_to_min(9, 0),
        'available_end': time_to_min(16, 0),
        'duration': 30,
        'location': 'Russian Hill',
    },
    'Daniel': {
        'available_start': time_to_min(8, 0),
        'available_end': time_to_min(13, 30),
        'duration': 15,
        'location': 'Golden Gate Park',
    },
    'Stephanie': {
        'available_start': time_to_min(20, 30),
        'available_end': time_to_min(22, 0),
        'duration': 90,
        'location': 'Mission District',
    },
}

travel_time = {
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'Mission District'): 24,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Mission District'): 10,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'Mission District'): 16,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Alamo Square'): 10,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Mission District', 'Sunset District'): 24,
    ('Mission District', 'Alamo Square'): 11,
    ('Mission District', 'Russian Hill'): 15,
    ('Mission District', 'Golden Gate Park'): 17,
}

s = Solver()

met = {name: Bool(f'met_{name}') for name in friends}
start = {name: Int(f'start_{name}') for name in friends}
end = {name: Int(f'end_{name}') for name in friends}

arrival_time = time_to_min(9, 0)  # 9:00 AM at Sunset District

for name in friends:
    data = friends[name]
    loc = data['location']
    initial_travel = travel_time[('Sunset District', loc)]
    
    # Basic constraints for availability and duration
    s.add(Implies(met[name], start[name] >= data['available_start']))
    s.add(Implies(met[name], end[name] == start[name] + data['duration']))
    s.add(Implies(met[name], end[name] <= data['available_end']))
    
    # Start time must be >= arrival + initial travel OR after another friend's end + travel
    constraints = [start[name] >= arrival_time + initial_travel]
    for other in friends:
        if other != name:
            other_loc = friends[other]['location']
            constraints.append(And(met[other], start[name] >= end[other] + travel_time[(other_loc, loc)]))
    s.add(Implies(met[name], Or(constraints)))

# Pairwise constraints for all friends
friend_names = list(friends.keys())
for i in range(len(friend_names)):
    for j in range(i + 1, len(friend_names)):
        a = friend_names[i]
        b = friend_names[j]
        a_loc = friends[a]['location']
        b_loc = friends[b]['location']
        time_ab = travel_time[(a_loc, b_loc)]
        time_ba = travel_time[(b_loc, a_loc)]
        
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