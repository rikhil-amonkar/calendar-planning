from z3 import *

# Define friends and their data
friends = [
    {'name': 'Emily', 'location': 'Alamo Square', 'start': 11*60+45, 'end': 15*60+15, 'duration': 105},
    {'name': 'Barbara', 'location': 'Union Square', 'start': 16*60+45, 'end': 18*60+15, 'duration': 60},
    {'name': 'William', 'location': 'Chinatown', 'start': 17*60+15, 'end': 19*60, 'duration': 105},
]

# Create travel times dictionary
travel_times = {
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'Chinatown'): 20,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'Chinatown'): 16,
    ('Union Square', 'The Castro'): 19,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Chinatown'): 7,
    ('Chinatown', 'The Castro'): 22,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'Union Square'): 7,
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

    solver.add(Implies(sched, end == start + duration))
    solver.add(Implies(sched, And(start >= avail_start, end <= avail_end)))
    solver.add(Implies(sched, pos >= 1))
    solver.add(Implies(Not(sched), pos == 0))

# Add pairwise ordering constraints
for i in range(len(friends)):
    a = friends[i]
    for j in range(i+1, len(friends)):
        b = friends[j]
        a_sched = a['scheduled']
        b_sched = b['scheduled']
        travel_ab = travel_times.get((a['location'], b['location']), 0)
        travel_ba = travel_times.get((b['location'], a['location']), 0)

        # At least one must be before the other if both are scheduled
        solver.add(Implies(And(a_sched, b_sched), 
                          Or(And(a['pos'] < b['pos'], b['start_time'] >= a['end_time'] + travel_ab),
                             And(b['pos'] < a['pos'], a['start_time'] >= b['end_time'] + travel_ba))))

# Initial position constraint (start at The Castro)
for friend in friends:
    loc = friend['location']
    sched = friend['scheduled']
    start = friend['start_time']
    solver.add(Implies(And(sched, friend['pos'] == 1), 
                      start >= 9*60 + travel_times[('The Castro', loc)]))

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