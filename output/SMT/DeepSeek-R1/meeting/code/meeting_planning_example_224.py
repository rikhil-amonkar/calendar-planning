from z3 import *

# Define friends and their data
friends = [
    {'name': 'Melissa', 'location': 'Golden Gate Park', 'start': 8*60+30, 'end': 20*60, 'duration': 15},
    {'name': 'Nancy', 'location': 'Presidio', 'start': 19*60+45, 'end': 22*60, 'duration': 105},
    {'name': 'Emily', 'location': 'Richmond District', 'start': 16*60+45, 'end': 22*60, 'duration': 120},
]

# Create travel times dictionary
travel_times = {
    ("Fisherman's Wharf", 'Golden Gate Park'): 25,
    ("Fisherman's Wharf", 'Presidio'): 17,
    ("Fisherman's Wharf", 'Richmond District'): 18,
    ('Golden Gate Park', "Fisherman's Wharf"): 24,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Presidio', "Fisherman's Wharf"): 19,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Richmond District'): 7,
    ('Richmond District', "Fisherman's Wharf"): 18,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Richmond District', 'Presidio'): 7,
}

solver = Optimize()

# Create variables for each friend
for friend in friends:
    name = friend['name']
    friend['scheduled'] = Bool(f'scheduled_{name}')
    friend['start_time'] = Int(f'start_{name}')
    friend['end_time'] = Int(f'end_{name}')
    friend['pos'] = Int(f'pos_{name}')

# Add constraints for each friend
for friend in friends:
    sched = friend['scheduled']
    start = friend['start_time']
    end = friend['end_time']
    pos = friend['pos']
    duration = friend['duration']
    avail_start = friend['start']
    avail_end = friend['end']
    loc = friend['location']

    # If scheduled, meeting fits in availability window and duration
    solver.add(Implies(sched, end == start + duration))
    solver.add(Implies(sched, And(start >= avail_start, end <= avail_end)))
    solver.add(Implies(sched, pos >= 1))
    solver.add(Implies(Not(sched), pos == 0))

# Add ordering and travel time constraints between friends
for i in range(len(friends)):
    a = friends[i]
    for j in range(i+1, len(friends)):
        b = friends[j]
        a_sched = a['scheduled']
        b_sched = b['scheduled']
        travel_ab = travel_times.get((a['location'], b['location']), 0)
        travel_ba = travel_times.get((b['location'], a['location']), 0)

        # Ordering constraint with travel time
        solver.add(Implies(And(a_sched, b_sched),
                          Or(And(a['pos'] < b['pos'], b['start_time'] >= a['end_time'] + travel_ab),
                             And(b['pos'] < a['pos'], a['start_time'] >= b['end_time'] + travel_ba))))

# Initial position constraint (start at Fisherman's Wharf)
for friend in friends:
    loc = friend['location']
    sched = friend['scheduled']
    start = friend['start_time']
    solver.add(Implies(And(sched, friend['pos'] == 1),
                      start >= 9*60 + travel_times[("Fisherman's Wharf", loc)]))

# Ensure unique positions for scheduled friends
solver.add(Distinct([If(f['scheduled'], f['pos'], 0) for f in friends]))

# Maximize number of scheduled friends
scheduled = [If(f['scheduled'], 1, 0) for f in friends]
solver.maximize(Sum(scheduled))

if solver.check() == sat:
    model = solver.model()
    result = []
    for f in friends:
        if model.evaluate(f['scheduled']):
            pos = model.evaluate(f['pos']).as_long()
            start = model.evaluate(f['start_time']).as_long()
            end = model.evaluate(f['end_time']).as_long()
            result.append((pos, f['name'], start, end))
    result.sort()
    print("Optimal Schedule:")
    for pos, name, start, end in result:
        print(f"{pos}: {name} {start//60:02}:{start%60:02} to {end//60:02}:{end%60:02}")
else:
    print("No valid schedule found.")