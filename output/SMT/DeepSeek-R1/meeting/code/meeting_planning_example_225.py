from z3 import *

def time_to_min(h, m):
    return h * 60 + m

friends = {
    'Sarah': {
        'available_start': time_to_min(16, 0),
        'available_end': time_to_min(18, 15),
        'duration': 60,
        'location': 'North Beach',
    },
    'Jeffrey': {
        'available_start': time_to_min(15, 0),
        'available_end': time_to_min(22, 0),
        'duration': 75,
        'location': 'Union Square',
    },
    'Brian': {
        'available_start': time_to_min(16, 0),
        'available_end': time_to_min(17, 30),
        'duration': 75,
        'location': 'Alamo Square',
    },
}

travel_time = {
    ('Sunset District', 'North Beach'): 29,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Alamo Square'): 17,
    ('North Beach', 'Sunset District'): 27,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Alamo Square'): 16,
    ('Union Square', 'Sunset District'): 26,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Alamo Square'): 15,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Union Square'): 14,
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