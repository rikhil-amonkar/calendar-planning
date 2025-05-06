from z3 import *

def time_to_min(h, m):
    return h * 60 + m

friends = {
    'William': {
        'available_start': time_to_min(15, 15),
        'available_end': time_to_min(17, 15),
        'duration': 60,
        'location': 'Alamo Square',
    },
    'Joshua': {
        'available_start': time_to_min(7, 0),
        'available_end': time_to_min(20, 0),
        'duration': 15,
        'location': 'Richmond District',
    },
    'Joseph': {
        'available_start': time_to_min(11, 15),
        'available_end': time_to_min(13, 30),
        'duration': 15,
        'location': 'Financial District',
    },
    'David': {
        'available_start': time_to_min(16, 45),
        'available_end': time_to_min(19, 15),
        'duration': 45,
        'location': 'Union Square',
    },
    'Brian': {
        'available_start': time_to_min(13, 45),
        'available_end': time_to_min(20, 45),
        'duration': 105,
        'location': 'Fisherman\'s Wharf',
    },
    'Karen': {
        'available_start': time_to_min(11, 30),
        'available_end': time_to_min(18, 30),
        'duration': 15,
        'location': 'Marina District',
    },
    'Anthony': {
        'available_start': time_to_min(7, 15),
        'available_end': time_to_min(10, 30),
        'duration': 30,
        'location': 'Haight-Ashbury',
    },
    'Matthew': {
        'available_start': time_to_min(17, 15),
        'available_end': time_to_min(19, 15),
        'duration': 120,
        'location': 'Mission District',
    },
    'Helen': {
        'available_start': time_to_min(8, 0),
        'available_end': time_to_min(12, 0),
        'duration': 75,
        'location': 'Pacific Heights',
    },
    'Jeffrey': {
        'available_start': time_to_min(19, 0),
        'available_end': time_to_min(21, 30),
        'duration': 60,
        'location': 'Golden Gate Park',
    },
}

travel_time = {
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Richmond District'): 16,
    ('The Castro', 'Financial District'): 21,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'Fisherman\'s Wharf'): 24,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('The Castro', 'Mission District'): 7,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Golden Gate Park'): 11,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Richmond District'): 11,
    ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'Fisherman\'s Wharf'): 19,
    ('Alamo Square', 'Marina District'): 15,
    ('Alamo Square', 'Haight-Ashbury'): 5,
    ('Alamo Square', 'Mission District'): 10,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Richmond District', 'The Castro'): 16,
    ('Richmond District', 'Alamo Square'): 13,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'Union Square'): 21,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'Haight-Ashbury'): 10,
    ('Richmond District', 'Mission District'): 20,
    ('Richmond District', 'Pacific Heights'): 10,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Financial District', 'The Castro'): 20,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'Union Square'): 9,
    ('Financial District', 'Fisherman\'s Wharf'): 10,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Financial District', 'Mission District'): 17,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Union Square', 'The Castro'): 17,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Richmond District'): 20,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Fisherman\'s Wharf'): 15,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'Mission District'): 14,
    ('Union Square', 'Pacific Heights'): 15,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Fisherman\'s Wharf', 'The Castro'): 27,
    ('Fisherman\'s Wharf', 'Alamo Square'): 21,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Fisherman\'s Wharf', 'Union Square'): 13,
    ('Fisherman\'s Wharf', 'Marina District'): 9,
    ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Fisherman\'s Wharf'): 10,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Mission District'): 20,
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Haight-Ashbury', 'Alamo Square'): 5,
    ('Haight-Ashbury', 'Richmond District'): 10,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Haight-Ashbury', 'Union Square'): 19,
    ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Mission District', 'The Castro'): 7,
    ('Mission District', 'Alamo Square'): 11,
    ('Mission District', 'Richmond District'): 20,
    ('Mission District', 'Financial District'): 15,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Marina District'): 19,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Pacific Heights', 'The Castro'): 16,
    ('Pacific Heights', 'Alamo Square'): 10,
    ('Pacific Heights', 'Richmond District'): 12,
    ('Pacific Heights', 'Financial District'): 13,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Marina District'): 6,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Alamo Square'): 9,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Golden Gate Park', 'Pacific Heights'): 16,
}

s = Solver()

met = {name: Bool(f'met_{name}') for name in friends}
start = {name: Int(f'start_{name}') for name in friends}
end = {name: Int(f'end_{name}') for name in friends}

arrival_time = time_to_min(9, 0)  # 9:00 AM at The Castro

# Individual constraints for each friend
for name in friends:
    data = friends[name]
    loc = data['location']
    initial_travel = travel_time[('The Castro', loc)]
    
    s.add(Implies(met[name], start[name] >= data['available_start']))
    s.add(Implies(met[name], start[name] >= arrival_time + initial_travel))
    s.add(Implies(met[name], end[name] == start[name] + data['duration']))
    s.add(Implies(met[name], end[name] <= data['available_end']))

# Pairwise constraints for all friend pairs
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

# Optimize to maximize number of friends met
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