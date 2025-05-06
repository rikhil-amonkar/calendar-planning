from z3 import *

def time_to_min(h, m):
    return h * 60 + m

friends = {
    'Emily': {
        'available_start': time_to_min(9, 15),
        'available_end': time_to_min(13, 45),
        'duration': 120,
        'location': 'Pacific Heights',
    },
    'Helen': {
        'available_start': time_to_min(13, 45),
        'available_end': time_to_min(18, 45),
        'duration': 30,
        'location': 'North Beach',
    },
    'Kimberly': {
        'available_start': time_to_min(18, 45),
        'available_end': time_to_min(21, 15),
        'duration': 75,
        'location': 'Golden Gate Park',
    },
    'James': {
        'available_start': time_to_min(10, 30),
        'available_end': time_to_min(11, 30),
        'duration': 30,
        'location': 'Embarcadero',
    },
    'Linda': {
        'available_start': time_to_min(7, 30),
        'available_end': time_to_min(19, 15),
        'duration': 15,
        'location': 'Haight-Ashbury',
    },
    'Paul': {
        'available_start': time_to_min(14, 45),
        'available_end': time_to_min(18, 45),
        'duration': 90,
        'location': 'Fisherman\'s Wharf',
    },
    'Anthony': {
        'available_start': time_to_min(8, 0),
        'available_end': time_to_min(14, 45),
        'duration': 105,
        'location': 'Mission District',
    },
    'Nancy': {
        'available_start': time_to_min(8, 30),
        'available_end': time_to_min(13, 45),
        'duration': 120,
        'location': 'Alamo Square',
    },
    'William': {
        'available_start': time_to_min(17, 30),
        'available_end': time_to_min(20, 30),
        'duration': 120,
        'location': 'Bayview',
    },
    'Margaret': {
        'available_start': time_to_min(15, 15),
        'available_end': time_to_min(18, 15),
        'duration': 45,
        'location': 'Richmond District',
    },
}

travel_time = {
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Fisherman\'s Wharf'): 7,
    ('Russian Hill', 'Mission District'): 16,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Bayview'): 23,
    ('Russian Hill', 'Richmond District'): 14,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Pacific Heights', 'North Beach'): 9,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'Embarcadero'): 10,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Alamo Square'): 10,
    ('Pacific Heights', 'Bayview'): 22,
    ('Pacific Heights', 'Richmond District'): 12,
    ('North Beach', 'Russian Hill'): 4,
    ('North Beach', 'Pacific Heights'): 8,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Embarcadero'): 6,
    ('North Beach', 'Haight-Ashbury'): 18,
    ('North Beach', 'Fisherman\'s Wharf'): 5,
    ('North Beach', 'Mission District'): 18,
    ('North Beach', 'Alamo Square'): 16,
    ('North Beach', 'Bayview'): 25,
    ('North Beach', 'Richmond District'): 18,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'North Beach'): 23,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Golden Gate Park', 'Alamo Square'): 9,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Embarcadero', 'Russian Hill'): 8,
    ('Embarcadero', 'Pacific Heights'): 11,
    ('Embarcadero', 'North Beach'): 5,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Haight-Ashbury'): 21,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Embarcadero', 'Mission District'): 20,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Embarcadero', 'Bayview'): 21,
    ('Embarcadero', 'Richmond District'): 21,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'North Beach'): 19,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'Embarcadero'): 20,
    ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Alamo Square'): 5,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'Richmond District'): 10,
    ('Fisherman\'s Wharf', 'Russian Hill'): 7,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'North Beach'): 6,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Fisherman\'s Wharf', 'Alamo Square'): 21,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
    ('Mission District', 'Russian Hill'): 15,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'North Beach'): 17,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Mission District', 'Embarcadero'): 19,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Alamo Square'): 11,
    ('Mission District', 'Bayview'): 14,
    ('Mission District', 'Richmond District'): 20,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Embarcadero'): 16,
    ('Alamo Square', 'Haight-Ashbury'): 5,
    ('Alamo Square', 'Fisherman\'s Wharf'): 19,
    ('Alamo Square', 'Mission District'): 10,
    ('Alamo Square', 'Bayview'): 16,
    ('Alamo Square', 'Richmond District'): 11,
    ('Bayview', 'Russian Hill'): 23,
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'North Beach'): 22,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Bayview', 'Embarcadero'): 19,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Mission District'): 13,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'Richmond District'): 25,
    ('Richmond District', 'Russian Hill'): 13,
    ('Richmond District', 'Pacific Heights'): 10,
    ('Richmond District', 'North Beach'): 17,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Haight-Ashbury'): 10,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Richmond District', 'Mission District'): 20,
    ('Richmond District', 'Alamo Square'): 13,
    ('Richmond District', 'Bayview'): 27,
}

s = Solver()

met = {name: Bool(f'met_{name}') for name in friends}
start = {name: Int(f'start_{name}') for name in friends}
end = {name: Int(f'end_{name}') for name in friends}

arrival_time = time_to_min(9, 0)  # 9:00 AM at Russian Hill

# Individual constraints for each friend
for name in friends:
    data = friends[name]
    loc = data['location']
    initial_travel = travel_time[('Russian Hill', loc)]
    
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
        time_ab = travel_time.get((a_loc, b_loc), 0)
        time_ba = travel_time.get((b_loc, a_loc), 0)
        
        s.add(Implies(And(met[a], met[b]), Or(
            end[a] + time_ab <= start[b],
            end[b] + time_ba <= start[a]
        ))

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