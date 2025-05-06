from z3 import *

def time_to_min(h, m):
    return h * 60 + m

friends = {
    'Helen': {
        'available_start': time_to_min(9, 30),
        'available_end': time_to_min(12, 15),
        'duration': 45,
        'location': 'Golden Gate Park',
    },
    'Steven': {
        'available_start': time_to_min(20, 15),
        'available_end': time_to_min(22, 0),
        'duration': 105,
        'location': 'The Castro',
    },
    'Deborah': {
        'available_start': time_to_min(8, 30),
        'available_end': time_to_min(12, 0),
        'duration': 30,
        'location': 'Bayview',
    },
    'Matthew': {
        'available_start': time_to_min(9, 15),
        'available_end': time_to_min(14, 15),
        'duration': 45,
        'location': 'Marina District',
    },
    'Joseph': {
        'available_start': time_to_min(14, 15),
        'available_end': time_to_min(18, 45),
        'duration': 120,
        'location': 'Union Square',
    },
    'Ronald': {
        'available_start': time_to_min(16, 0),
        'available_end': time_to_min(20, 45),
        'duration': 60,
        'location': 'Sunset District',
    },
    'Robert': {
        'available_start': time_to_min(18, 30),
        'available_end': time_to_min(21, 15),
        'duration': 120,
        'location': 'Alamo Square',
    },
    'Rebecca': {
        'available_start': time_to_min(14, 45),
        'available_end': time_to_min(16, 15),
        'duration': 30,
        'location': 'Financial District',
    },
    'Elizabeth': {
        'available_start': time_to_min(18, 30),
        'available_end': time_to_min(21, 0),
        'duration': 120,
        'location': 'Mission District',
    },
}

travel_time = {
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'The Castro'): 16,
    ('Pacific Heights', 'Bayview'): 22,
    ('Pacific Heights', 'Marina District'): 6,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'Sunset District'): 21,
    ('Pacific Heights', 'Alamo Square'): 10,
    ('Pacific Heights', 'Financial District'): 13,
    ('Pacific Heights', 'Mission District'): 15,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Alamo Square'): 9,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Mission District'): 17,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Golden Gate Park'): 11,
    ('The Castro', 'Bayview'): 19,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'Sunset District'): 17,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Financial District'): 21,
    ('The Castro', 'Mission District'): 7,
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Bayview', 'The Castro'): 19,
    ('Bayview', 'Marina District'): 27,
    ('Bayview', 'Union Square'): 18,
    ('Bayview', 'Sunset District'): 23,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'Financial District'): 19,
    ('Bayview', 'Mission District'): 13,
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Mission District'): 20,
    ('Union Square', 'Pacific Heights'): 15,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'The Castro'): 17,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Sunset District'): 27,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Mission District'): 14,
    ('Sunset District', 'Pacific Heights'): 21,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Bayview'): 22,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'Mission District'): 25,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Bayview'): 16,
    ('Alamo Square', 'Marina District'): 15,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'Mission District'): 10,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'The Castro'): 20,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Union Square'): 9,
    ('Financial District', 'Sunset District'): 30,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Mission District'): 17,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Mission District', 'The Castro'): 7,
    ('Mission District', 'Bayview'): 14,
    ('Mission District', 'Marina District'): 19,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Sunset District'): 24,
    ('Mission District', 'Alamo Square'): 11,
    ('Mission District', 'Financial District'): 15,
}

s = Solver()

met = {name: Bool(f'met_{name}') for name in friends}
start = {name: Int(f'start_{name}') for name in friends}
end = {name: Int(f'end_{name}') for name in friends}

arrival_time = time_to_min(9, 0)  # 9:00 AM at Pacific Heights

for name in friends:
    data = friends[name]
    loc = data['location']
    initial_travel = travel_time[('Pacific Heights', loc)]
    
    # Basic constraints for availability and duration
    s.add(Implies(met[name], start[name] >= data['available_start']))
    s.add(Implies(met[name], end[name] == start[name] + data['duration']))
    s.add(Implies(met[name], end[name] <= data['available_end']))
    
    # Start time must be >= arrival + initial travel OR after another friend's end + travel
    other_friends = [other for other in friends if other != name]
    constraints = [start[name] >= arrival_time + initial_travel]
    for other in other_friends:
        other_loc = friends[other]['location']
        travel_t = travel_time[(other_loc, loc)]
        constraints.append(And(met[other], start[name] >= end[other] + travel_t))
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