from z3 import *

# Define friends and their data
friends = [
    {'name': 'Betty', 'location': 'Russian Hill', 'start': 7*60, 'end': 16*60+45, 'duration': 105},
    {'name': 'Melissa', 'location': 'Alamo Square', 'start': 9*60+30, 'end': 17*60+15, 'duration': 105},
    {'name': 'Joshua', 'location': 'Haight-Ashbury', 'start': 12*60+15, 'end': 19*60, 'duration': 90},
    {'name': 'Jeffrey', 'location': 'Marina District', 'start': 12*60+15, 'end': 18*60, 'duration': 45},
    {'name': 'James', 'location': 'Bayview', 'start': 7*60+30, 'end': 20*60, 'duration': 90},
    {'name': 'Anthony', 'location': 'Chinatown', 'start': 11*60+45, 'end': 13*60+30, 'duration': 75},
    {'name': 'Timothy', 'location': 'Presidio', 'start': 12*60+30, 'end': 14*60+45, 'duration': 90},
    {'name': 'Emily', 'location': 'Sunset District', 'start': 19*60+30, 'end': 21*60+30, 'duration': 120},
]

# Create travel times dictionary
travel_times = {
    ('Union Square', 'Russian Hill'): 13,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Sunset District'): 27,
    ('Russian Hill', 'Union Square'): 10,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'Bayview'): 23,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Sunset District'): 23,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'Haight-Ashbury'): 5,
    ('Alamo Square', 'Marina District'): 15,
    ('Alamo Square', 'Bayview'): 16,
    ('Alamo Square', 'Chinatown'): 15,
    ('Alamo Square', 'Presidio'): 17,
    ('Alamo Square', 'Sunset District'): 16,
    ('Haight-Ashbury', 'Union Square'): 19,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'Alamo Square'): 5,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'Chinatown'): 19,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Chinatown'): 15,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'Sunset District'): 19,
    ('Bayview', 'Union Square'): 18,
    ('Bayview', 'Russian Hill'): 23,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Marina District'): 27,
    ('Bayview', 'Chinatown'): 19,
    ('Bayview', 'Presidio'): 32,
    ('Bayview', 'Sunset District'): 23,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Russian Hill'): 7,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'Haight-Ashbury'): 19,
    ('Chinatown', 'Marina District'): 12,
    ('Chinatown', 'Bayview'): 20,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Sunset District'): 29,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'Alamo Square'): 19,
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'Bayview'): 31,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'Sunset District'): 15,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Bayview'): 22,
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'Presidio'): 16,
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
    name = friend['name']
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
    solver.add(sched == (pos >= 1))
    solver.add(Implies(Not(sched), pos == 0))
    solver.add(pos >= 0, pos <= len(friends))

# Add pairwise constraints
for i in range(len(friends)):
    a = friends[i]
    a_name = a['name']
    a_loc = a['location']
    for j in range(i + 1, len(friends)):
        b = friends[j]
        b_name = b['name']
        b_loc = b['location']

        travel_ab = travel_times[(a_loc, b_loc)]
        travel_ba = travel_times[(b_loc, a_loc)]

        a_sched = a['scheduled']
        b_sched = b['scheduled']

        solver.add(Implies(And(a_sched, b_sched), a['pos'] != b['pos']))

        a_before_b = a['pos'] < b['pos']

        solver.add(Implies(And(a_sched, b_sched, a_before_b),
                          b['start_time'] >= a['end_time'] + travel_ab))
        solver.add(Implies(And(a_sched, b_sched, Not(a_before_b)),
                          a['start_time'] >= b['end_time'] + travel_ba))

# Add constraints for first friend
for friend in friends:
    loc = friend['location']
    sched = friend['scheduled']
    start = friend['start_time']
    pos = friend['pos']

    travel = travel_times[('Union Square', loc)]
    solver.add(Implies(And(sched, pos == 1), start >= 540 + travel))

# Maximize the number of scheduled friends
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