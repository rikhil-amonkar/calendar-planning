from z3 import *

def time_to_min(h, m):
    return h * 60 + m

friends = {
    'Lisa': {
        'available_start': time_to_min(19, 15),
        'available_end': time_to_min(21, 15),
        'duration': 120,
        'location': 'The Castro',
    },
    'Daniel': {
        'available_start': time_to_min(8, 15),
        'available_end': time_to_min(11, 0),
        'duration': 15,
        'location': 'Nob Hill',
    },
    'Elizabeth': {
        'available_start': time_to_min(21, 15),
        'available_end': time_to_min(22, 15),
        'duration': 45,
        'location': 'Presidio',
    },
    'Steven': {
        'available_start': time_to_min(16, 30),
        'available_end': time_to_min(20, 45),
        'duration': 90,
        'location': 'Marina District',
    },
    'Timothy': {
        'available_start': time_to_min(12, 0),
        'available_end': time_to_min(18, 0),
        'duration': 90,
        'location': 'Pacific Heights',
    },
    'Ashley': {
        'available_start': time_to_min(20, 45),
        'available_end': time_to_min(21, 45),
        'duration': 60,
        'location': 'Golden Gate Park',
    },
    'Kevin': {
        'available_start': time_to_min(12, 0),
        'available_end': time_to_min(19, 0),
        'duration': 30,
        'location': 'Chinatown',
    },
    'Betty': {
        'available_start': time_to_min(13, 15),
        'available_end': time_to_min(15, 45),
        'duration': 30,
        'location': 'Richmond District',
    },
}

travel_time = {
    ('Mission District', 'The Castro'): 7,
    ('Mission District', 'Nob Hill'): 12,
    ('Mission District', 'Presidio'): 25,
    ('Mission District', 'Marina District'): 19,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Mission District', 'Chinatown'): 16,
    ('Mission District', 'Richmond District'): 20,
    ('The Castro', 'Mission District'): 7,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Presidio'): 20,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Golden Gate Park'): 11,
    ('The Castro', 'Chinatown'): 22,
    ('The Castro', 'Richmond District'): 16,
    ('Nob Hill', 'Mission District'): 13,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Presidio'): 17,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'Golden Gate Park'): 17,
    ('Nob Hill', 'Chinatown'): 6,
    ('Nob Hill', 'Richmond District'): 14,
    ('Presidio', 'Mission District'): 26,
    ('Presidio', 'The Castro'): 21,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'Pacific Heights'): 11,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'Richmond District'): 7,
    ('Marina District', 'Mission District'): 20,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Marina District', 'Chinatown'): 15,
    ('Marina District', 'Richmond District'): 11,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'The Castro'): 16,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Presidio'): 11,
    ('Pacific Heights', 'Marina District'): 6,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'Chinatown'): 11,
    ('Pacific Heights', 'Richmond District'): 12,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Chinatown', 'Mission District'): 17,
    ('Chinatown', 'The Castro'): 22,
    ('Chinatown', 'Nob Hill'): 9,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Marina District'): 12,
    ('Chinatown', 'Pacific Heights'): 10,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Richmond District'): 20,
    ('Richmond District', 'Mission District'): 20,
    ('Richmond District', 'The Castro'): 16,
    ('Richmond District', 'Nob Hill'): 17,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'Pacific Heights'): 10,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Richmond District', 'Chinatown'): 20,
}

s = Solver()

met = {name: Bool(f'met_{name}') for name in friends}
start = {name: Int(f'start_{name}') for name in friends}
end = {name: Int(f'end_{name}') for name in friends}

arrival_time = time_to_min(9, 0)  # 9:00 AM at Mission District

for name in friends:
    data = friends[name]
    loc = data['location']
    initial_travel = travel_time[('Mission District', loc)]
    
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