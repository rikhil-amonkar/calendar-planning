from z3 import *

def time_to_min(h, m):
    return h * 60 + m

friends = {
    'Stephanie': {
        'available_start': time_to_min(8, 15),
        'available_end': time_to_min(13, 45),
        'duration': 90,
        'location': 'Mission District',
    },
    'Sandra': {
        'available_start': time_to_min(13, 0),
        'available_end': time_to_min(19, 30),
        'duration': 15,
        'location': 'Bayview',
    },
    'Richard': {
        'available_start': time_to_min(7, 15),
        'available_end': time_to_min(10, 15),
        'duration': 75,
        'location': 'Pacific Heights',
    },
    'Brian': {
        'available_start': time_to_min(12, 15),
        'available_end': time_to_min(16, 0),
        'duration': 120,
        'location': 'Russian Hill',
    },
    'Jason': {
        'available_start': time_to_min(8, 30),
        'available_end': time_to_min(17, 45),
        'duration': 60,
        'location': 'Fisherman\'s Wharf',
    },
}

travel_time = {
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Bayview'): 15,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Russian Hill'): 15,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Mission District'): 13,
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'Russian Hill'): 23,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Bayview'): 22,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Mission District'): 16,
    ('Russian Hill', 'Bayview'): 23,
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Russian Hill', 'Fisherman\'s Wharf'): 7,
    ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'Russian Hill'): 7,
}

s = Solver()

met = {name: Bool(f'met_{name}') for name in friends}
start = {name: Int(f'start_{name}') for name in friends}
end = {name: Int(f'end_{name}') for name in friends}

arrival_time = time_to_min(9, 0)  # 9:00 AM at Haight-Ashbury

for name in friends:
    data = friends[name]
    loc = data['location']
    initial_travel = travel_time[('Haight-Ashbury', loc)]
    
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