from z3 import *

def to_minutes(h, m):
    return h * 60 + m

def to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

friends = [
    {'name': 'Charles', 'location': 'Bayview', 
     'start': to_minutes(11,30), 'end': to_minutes(14,30), 'duration':45},
    {'name': 'Robert', 'location': 'Sunset District', 
     'start': to_minutes(16,45), 'end': to_minutes(21,0), 'duration':30},
    {'name': 'Karen', 'location': 'Richmond District', 
     'start': to_minutes(19,15), 'end': to_minutes(21,30), 'duration':60},
    {'name': 'Rebecca', 'location': 'Nob Hill', 
     'start': to_minutes(16,15), 'end': to_minutes(20,30), 'duration':90},
    {'name': 'Margaret', 'location': 'Chinatown', 
     'start': to_minutes(14,15), 'end': to_minutes(19,45), 'duration':120},
    {'name': 'Patricia', 'location': 'Haight-Ashbury', 
     'start': to_minutes(14,30), 'end': to_minutes(20,30), 'duration':45},
    {'name': 'Mark', 'location': 'North Beach', 
     'start': to_minutes(14,0), 'end': to_minutes(18,30), 'duration':105},
    {'name': 'Melissa', 'location': 'Russian Hill', 
     'start': to_minutes(13,0), 'end': to_minutes(19,45), 'duration':30},
    {'name': 'Laura', 'location': 'Embarcadero', 
     'start': to_minutes(7,45), 'end': to_minutes(13,15), 'duration':105},
]

travel_times = {
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Chinatown'): 15,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'North Beach'): 11,
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'Embarcadero'): 14,
    ('Bayview', 'Marina District'): 27,
    ('Bayview', 'Sunset District'): 23,
    ('Bayview', 'Richmond District'): 25,
    ('Bayview', 'Nob Hill'): 20,
    ('Bayview', 'Chinatown'): 19,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'North Beach'): 22,
    ('Bayview', 'Russian Hill'): 23,
    ('Bayview', 'Embarcadero'): 19,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Bayview'): 22,
    ('Sunset District', 'Richmond District'): 12,
    ('Sunset District', 'Nob Hill'): 27,
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'North Beach'): 28,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Embarcadero'): 30,
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'Bayview'): 27,
    ('Richmond District', 'Sunset District'): 11,
    ('Richmond District', 'Nob Hill'): 17,
    ('Richmond District', 'Chinatown'): 20,
    ('Richmond District', 'Haight-Ashbury'): 10,
    ('Richmond District', 'North Beach'): 17,
    ('Richmond District', 'Russian Hill'): 13,
    ('Richmond District', 'Embarcadero'): 19,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'Bayview'): 19,
    ('Nob Hill', 'Sunset District'): 24,
    ('Nob Hill', 'Richmond District'): 14,
    ('Nob Hill', 'Chinatown'): 6,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Chinatown', 'Marina District'): 12,
    ('Chinatown', 'Bayview'): 20,
    ('Chinatown', 'Sunset District'): 29,
    ('Chinatown', 'Richmond District'): 20,
    ('Chinatown', 'Nob Hill'): 9,
    ('Chinatown', 'Haight-Ashbury'): 19,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', 'Russian Hill'): 7,
    ('Chinatown', 'Embarcadero'): 5,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Richmond District'): 10,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'Chinatown'): 19,
    ('Haight-Ashbury', 'North Beach'): 19,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'Embarcadero'): 20,
    ('North Beach', 'Marina District'): 9,
    ('North Beach', 'Bayview'): 25,
    ('North Beach', 'Sunset District'): 27,
    ('North Beach', 'Richmond District'): 18,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Haight-Ashbury'): 18,
    ('North Beach', 'Russian Hill'): 4,
    ('North Beach', 'Embarcadero'): 6,
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'Bayview'): 23,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Richmond District'): 14,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Embarcadero', 'Marina District'): 12,
    ('Embarcadero', 'Bayview'): 21,
    ('Embarcadero', 'Sunset District'): 30,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Chinatown'): 7,
    ('Embarcadero', 'Haight-Ashbury'): 21,
    ('Embarcadero', 'North Beach'): 5,
    ('Embarcadero', 'Russian Hill'): 8,
}

opt = Optimize()
meet = {f['name']: Bool(f"meet_{f['name']}") for f in friends}
start = {f['name']: Int(f"start_{f['name']}") for f in friends}
end = {f['name']: Int(f"end_{f['name']}") for f in friends}
initial_time = to_minutes(9, 0)

for f in friends:
    name = f['name']
    loc = f['location']
    s = f['start']
    e = f['end']
    d = f['duration']
    opt.add(Implies(meet[name], And(start[name] >= s, end[name] == start[name] + d, end[name] <= e)))
    from_marina = travel_times[('Marina District', loc)]
    arrival_conds = [start[name] >= initial_time + from_marina]
    for other in friends:
        if other['name'] == name:
            continue
        other_loc = other['location']
        travel = travel_times.get((other_loc, loc))
        if travel is not None:
            arrival_conds.append(And(meet[other['name']], start[name] >= end[other['name']] + travel))
    opt.add(Implies(meet[name], Or(arrival_conds)))

for i in range(len(friends)):
    for j in range(i+1, len(friends)):
        f1, f2 = friends[i], friends[j]
        n1, n2 = f1['name'], f2['name']
        loc1, loc2 = f1['location'], f2['location']
        t1 = travel_times.get((loc1, loc2))
        t2 = travel_times.get((loc2, loc1))
        opt.add(Implies(And(meet[n1], meet[n2]),
                       Or(end[n1] + t1 <= start[n2], end[n2] + t2 <= start[n1])))

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
    current_loc = 'Marina District'
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