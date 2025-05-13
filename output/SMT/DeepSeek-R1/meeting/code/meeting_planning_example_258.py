from z3 import *

def to_minutes(h, m):
    return h * 60 + m

def to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

friends = [
    {'name': 'Betty', 'location': 'Presidio', 
     'start': to_minutes(10,15), 'end': to_minutes(21,30), 'duration':45},
    {'name': 'David', 'location': 'Richmond District', 
     'start': to_minutes(13,0), 'end': to_minutes(20,15), 'duration':90},
    {'name': 'Barbara', 'location': 'Fisherman\'s Wharf', 
     'start': to_minutes(9,15), 'end': to_minutes(20,15), 'duration':120},
]

travel_times = {
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
}

opt = Optimize()
meet = {f['name']: Bool(f"meet_{f['name']}") for f in friends}
start = {f['name']: Int(f"start_{f['name']}") for f in friends}
end = {f['name']: Int(f"end_{f['name']}") for f in friends}
initial_time = to_minutes(9, 0)

# Base constraints for meeting times and durations
for f in friends:
    name = f['name']
    loc = f['location']
    s = f['start']
    e = f['end']
    d = f['duration']
    opt.add(Implies(meet[name], And(start[name] >= s, end[name] == start[name] + d, end[name] <= e)))
    
    # Arrival from Embarcadero
    travel = travel_times[('Embarcadero', loc)]
    opt.add(Implies(meet[name], start[name] >= initial_time + travel))
    
    # Constraints for travel between locations
    for other in friends:
        if other['name'] == name:
            continue
        other_loc = other['location']
        travel_time = travel_times.get((other_loc, loc))
        if travel_time is not None:
            opt.add(Implies(And(meet[name], meet[other['name']]),
                           Or(end[other['name']] + travel_time <= start[name],
                              end[name] + travel_times[(loc, other_loc)] <= start[other['name']])))

# No overlapping meetings with travel consideration
for i in range(len(friends)):
    for j in range(i+1, len(friends)):
        f1, f2 = friends[i], friends[j]
        t1 = travel_times.get((f1['location'], f2['location']))
        t2 = travel_times.get((f2['location'], f1['location']))
        if t1 is not None and t2 is not None:
            opt.add(Implies(And(meet[f1['name']], meet[f2['name']]),
                           Or(end[f1['name']] + t1 <= start[f2['name']],
                              end[f2['name']] + t2 <= start[f1['name']])))

total = Sum([If(meet[f['name']], 1, 0) for f in friends])
opt.maximize(total)

if opt.check() == sat:
    m = opt.model()
    scheduled = []
    for f in friends:
        name = f['name']
        if m.evaluate(meet[name]):
            s = m.evaluate(start[name]).as_long()
            e = m.evaluate(end[name]).as_long()
            scheduled.append((s, e, name, f['location']))
    scheduled.sort()
    
    current_loc = 'Embarcadero'
    current_time = initial_time
    print("Optimal Schedule:")
    for s, e, name, loc in scheduled:
        travel = travel_times.get((current_loc, loc), 0)
        depart_time = s - travel
        print(f"{to_time(depart_time)} - Travel from {current_loc} to {loc} ({travel} min)")
        print(f"{to_time(s)} - Meet {name} until {to_time(e)}")
        current_loc = loc
        current_time = e
else:
    print("No valid schedule found.")