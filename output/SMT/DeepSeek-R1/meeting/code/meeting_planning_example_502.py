from z3 import *

def time_to_min(h, m):
    return h * 60 + m

friends = {
    'Stephanie': {
        'available_start': time_to_min(11, 0),
        'available_end': time_to_min(15, 0),
        'duration': 105,
        'location': 'Golden Gate Park',
    },
    'Karen': {
        'available_start': time_to_min(13, 45),
        'available_end': time_to_min(16, 30),
        'duration': 15,
        'location': 'Chinatown',
    },
    'Brian': {
        'available_start': time_to_min(15, 0),
        'available_end': time_to_min(17, 15),
        'duration': 30,
        'location': 'Union Square',
    },
    'Rebecca': {
        'available_start': time_to_min(8, 0),
        'available_end': time_to_min(11, 15),
        'duration': 30,
        'location': 'Fisherman\'s Wharf',
    },
    'Joseph': {
        'available_start': time_to_min(8, 15),
        'available_end': time_to_min(9, 30),
        'duration': 60,
        'location': 'Pacific Heights',
    },
    'Steven': {
        'available_start': time_to_min(14, 30),
        'available_end': time_to_min(20, 45),
        'duration': 120,
        'location': 'North Beach',
    },
}

travel_time = {
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Chinatown'): 5,
    ('Financial District', 'Union Square'): 9,
    ('Financial District', 'Fisherman\'s Wharf'): 10,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'North Beach'): 7,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'North Beach'): 24,
    ('Chinatown', 'Financial District'): 5,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Fisherman\'s Wharf'): 8,
    ('Chinatown', 'Pacific Heights'): 10,
    ('Chinatown', 'North Beach'): 3,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Fisherman\'s Wharf'): 15,
    ('Union Square', 'Pacific Heights'): 15,
    ('Union Square', 'North Beach'): 10,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Fisherman\'s Wharf', 'Chinatown'): 12,
    ('Fisherman\'s Wharf', 'Union Square'): 13,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'North Beach'): 6,
    ('Pacific Heights', 'Financial District'): 13,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'Chinatown'): 11,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'North Beach'): 9,
    ('North Beach', 'Financial District'): 8,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Fisherman\'s Wharf'): 5,
    ('North Beach', 'Pacific Heights'): 8,
}

s = Solver()

met = {name: Bool(f'met_{name}') for name in friends}
start = {name: Int(f'start_{name}') for name in friends}
end = {name: Int(f'end_{name}') for name in friends}

arrival_time = time_to_min(9, 0)  # 9:00 AM at Financial District

for name in friends:
    data = friends[name]
    loc = data['location']
    initial_travel = travel_time[('Financial District', loc)]
    
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