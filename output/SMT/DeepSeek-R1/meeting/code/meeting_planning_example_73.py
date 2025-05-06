from z3 import *

def time_to_min(h, m):
    return h * 60 + m

friends = {
    'Barbara': {
        'available_start': time_to_min(7, 15),
        'available_end': time_to_min(22, 0),
        'duration': 60,
        'location': 'Pacific Heights',
    }
}

travel_time = {
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Pacific Heights', 'Russian Hill'): 7,
}

s = Solver()

met = {name: Bool(f'met_{name}') for name in friends}
start = {name: Int(f'start_{name}') for name in friends}
end = {name: Int(f'end_{name}') for name in friends}

arrival_time = time_to_min(9, 0)  # 9:00 AM at Russian Hill

for name in friends:
    data = friends[name]
    loc = data['location']
    initial_travel = travel_time[('Russian Hill', loc)]
    
    s.add(Implies(met[name], start[name] >= arrival_time + initial_travel))
    s.add(Implies(met[name], end[name] == start[name] + data['duration']))
    s.add(Implies(met[name], end[name] <= data['available_end']))
    s.add(Implies(met[name], start[name] >= data['available_start']))

# No pairwise constraints needed for single friend

opt = Optimize()
opt.add(s.assertions())
opt.maximize(Sum([If(met[name], 1, 0) for name in friends]))

if opt.check() == sat:
    m = opt.model()
    total = sum(1 for name in friends if m.evaluate(met[name]))
    print(f"SOLUTION: Met {total} friends.")
    for name in friends:
        if m.evaluate(met[name]):
            s_min = m.evaluate(start[name]).as_long()
            e_min = m.evaluate(end[name]).as_long()
            s_h, s_m = divmod(s_min, 60)
            e_h, e_m = divmod(e_min, 60)
            print(f"{name}: {s_h:02}:{s_m:02} to {e_h:02}:{e_m:02}")
else:
    print("No solution found.")