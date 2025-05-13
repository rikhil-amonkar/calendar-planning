from z3 import *

# Define friends and their data
friends = [
    {'name': 'David', 'location': "Fisherman's Wharf", 'start': 10*60+45, 'end': 15*60+30, 'duration': 15},
    {'name': 'Timothy', 'location': 'Pacific Heights', 'start': 9*60, 'end': 15*60+30, 'duration': 75},
    {'name': 'Robert', 'location': 'Mission District', 'start': 12*60+15, 'end': 19*60+45, 'duration': 90},
]

# Create travel times dictionary
travel_times = {
    ('Financial District', "Fisherman's Wharf"): 10,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'Mission District'): 17,
    ("Fisherman's Wharf", 'Financial District'): 11,
    ("Fisherman's Wharf", 'Pacific Heights'): 12,
    ("Fisherman's Wharf", 'Mission District'): 22,
    ('Pacific Heights', 'Financial District'): 13,
    ('Pacific Heights', "Fisherman's Wharf"): 13,
    ('Pacific Heights', 'Mission District'): 15,
    ('Mission District', 'Financial District'): 17,
    ('Mission District', "Fisherman's Wharf"): 22,
    ('Mission District', 'Pacific Heights'): 16,
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

# Initial position constraint (start at Financial District)
for friend in friends:
    loc = friend['location']
    sched = friend['scheduled']
    start = friend['start_time']
    solver.add(Implies(And(sched, friend['pos'] == 1),
                      start >= 9*60 + travel_times[('Financial District', loc)]))

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