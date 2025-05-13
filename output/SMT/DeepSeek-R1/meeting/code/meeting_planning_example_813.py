from z3 import *

# Define friends and their data
friends = [
    {'name': 'Joshua', 'location': 'Embarcadero', 'start': 9*60+45, 'end': 18*60, 'duration': 105},
    {'name': 'Jeffrey', 'location': 'Bayview', 'start': 9*60+45, 'end': 20*60+15, 'duration': 75},
    {'name': 'Charles', 'location': 'Union Square', 'start': 10*60+45, 'end': 20*60+15, 'duration': 120},
    {'name': 'Joseph', 'location': 'Chinatown', 'start': 7*60, 'end': 15*60+30, 'duration': 60},
    {'name': 'Elizabeth', 'location': 'Sunset District', 'start': 9*60, 'end': 9*60+45, 'duration': 45},
    {'name': 'Matthew', 'location': 'Golden Gate Park', 'start': 11*60, 'end': 19*60+30, 'duration': 45},
    {'name': 'Carol', 'location': 'Financial District', 'start': 10*60+45, 'end': 11*60+15, 'duration': 15},
    {'name': 'Paul', 'location': 'Haight-Ashbury', 'start': 19*60+15, 'end': 20*60+30, 'duration': 15},
    {'name': 'Rebecca', 'location': 'Mission District', 'start': 17*60, 'end': 21*60+45, 'duration': 45},
]

# Create travel times dictionary
travel_times = {
    ('Marina District', 'Embarcadero'): 14,
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Chinatown'): 15,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Mission District'): 20,
    ('Embarcadero', 'Marina District'): 12,
    ('Embarcadero', 'Bayview'): 21,
    ('Embarcadero', 'Union Square'): 10,
    ('Embarcadero', 'Chinatown'): 7,
    ('Embarcadero', 'Sunset District'): 30,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'Haight-Ashbury'): 21,
    ('Embarcadero', 'Mission District'): 20,
    ('Bayview', 'Marina District'): 27,
    ('Bayview', 'Embarcadero'): 19,
    ('Bayview', 'Union Square'): 18,
    ('Bayview', 'Chinatown'): 19,
    ('Bayview', 'Sunset District'): 23,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Bayview', 'Financial District'): 19,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Mission District'): 13,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Embarcadero'): 11,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Sunset District'): 27,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'Mission District'): 14,
    ('Chinatown', 'Marina District'): 12,
    ('Chinatown', 'Embarcadero'): 5,
    ('Chinatown', 'Bayview'): 20,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Sunset District'): 29,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Financial District'): 5,
    ('Chinatown', 'Haight-Ashbury'): 19,
    ('Chinatown', 'Mission District'): 17,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Embarcadero'): 30,
    ('Sunset District', 'Bayview'): 22,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Mission District'): 25,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Union Square'): 9,
    ('Financial District', 'Chinatown'): 5,
    ('Financial District', 'Sunset District'): 30,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Financial District', 'Mission District'): 17,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Embarcadero'): 20,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'Union Square'): 19,
    ('Haight-Ashbury', 'Chinatown'): 19,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Mission District', 'Marina District'): 19,
    ('Mission District', 'Embarcadero'): 19,
    ('Mission District', 'Bayview'): 14,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Chinatown'): 16,
    ('Mission District', 'Sunset District'): 24,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Mission District', 'Financial District'): 15,
    ('Mission District', 'Haight-Ashbury'): 12,
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

# Initial position constraint (start at Marina District)
for friend in friends:
    loc = friend['location']
    sched = friend['scheduled']
    start = friend['start_time']
    solver.add(Implies(And(sched, friend['pos'] == 1),
                      start >= 9*60 + travel_times.get(('Marina District', loc), 0)))

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