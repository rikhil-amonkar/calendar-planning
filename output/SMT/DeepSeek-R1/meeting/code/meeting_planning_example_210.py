from z3 import *

def time_to_min(h, m):
    return h * 60 + m

friends = {
    'Emily': {
        'available_start': time_to_min(16, 15),
        'available_end': time_to_min(21, 0),
        'duration': 105,
        'location': 'Presidio',
    },
    'Joseph': {
        'available_start': time_to_min(17, 15),
        'available_end': time_to_min(22, 0),
        'duration': 120,
        'location': 'Richmond District',
    },
    'Melissa': {
        'available_start': time_to_min(15, 45),
        'available_end': time_to_min(21, 45),
        'duration': 75,
        'location': 'Financial District',
    },
}

travel_time = {
    ("Fisherman's Wharf", 'Presidio'): 17,
    ("Fisherman's Wharf", 'Richmond District'): 18,
    ("Fisherman's Wharf", 'Financial District'): 11,
    ('Presidio', "Fisherman's Wharf"): 19,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Financial District'): 23,
    ('Richmond District', "Fisherman's Wharf"): 18,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Financial District'): 22,
    ('Financial District', "Fisherman's Wharf"): 10,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Richmond District'): 21,
}

s = Solver()

met = {name: Bool(f'met_{name}') for name in friends}
start = {name: Int(f'start_{name}') for name in friends}
end = {name: Int(f'end_{name}') for name in friends}

arrival_time = time_to_min(9, 0)  # 9:00 AM at Fisherman's Wharf

for name in friends:
    data = friends[name]
    s.add(Implies(met[name], start[name] >= data['available_start']))
    s.add(Implies(met[name], end[name] <= data['available_end']))
    s.add(Implies(met[name], end[name] == start[name] + data['duration']))

    loc = data['location']
    initial_travel = travel_time.get(("Fisherman's Wharf", loc), 0)
    clauses = [start[name] >= arrival_time + initial_travel]
    for other in friends:
        if other == name:
            continue
        other_loc = friends[other]['location']
        travel = travel_time.get((other_loc, loc), 0)
        clauses.append(And(met[other], start[name] >= end[other] + travel))
    s.add(Implies(met[name], Or(clauses)))

friend_names = list(friends.keys())
for i in range(len(friend_names)):
    for j in range(i + 1, len(friend_names)):
        X, Y = friend_names[i], friend_names[j]
        X_loc = friends[X]['location']
        Y_loc = friends[Y]['location']
        time_X_to_Y = travel_time.get((X_loc, Y_loc), 0)
        time_Y_to_X = travel_time.get((Y_loc, X_loc), 0)
        s.add(Or(
            Not(And(met[X], met[Y])),
            And(met[X], met[Y], end[X] + time_X_to_Y <= start[Y]),
            And(met[X], met[Y], end[Y] + time_Y_to_X <= start[X])
        ))

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