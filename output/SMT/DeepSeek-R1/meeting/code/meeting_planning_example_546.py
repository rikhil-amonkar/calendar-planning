from z3 import *

# Define travel times between locations
travel_time = {
    'Embarcadero': {
        'Richmond District': 21,
        'Union Square': 10,
        'Financial District': 5,
        'Pacific Heights': 11,
        'Nob Hill': 10,
        'Bayview': 21,
    },
    'Richmond District': {
        'Embarcadero': 19,
        'Union Square': 21,
        'Financial District': 22,
        'Pacific Heights': 10,
        'Nob Hill': 17,
        'Bayview': 26,
    },
    'Union Square': {
        'Embarcadero': 11,
        'Richmond District': 20,
        'Financial District': 9,
        'Pacific Heights': 15,
        'Nob Hill': 9,
        'Bayview': 15,
    },
    'Financial District': {
        'Embarcadero': 4,
        'Richmond District': 21,
        'Union Square': 9,
        'Pacific Heights': 13,
        'Nob Hill': 8,
        'Bayview': 19,
    },
    'Pacific Heights': {
        'Embarcadero': 10,
        'Richmond District': 12,
        'Union Square': 12,
        'Financial District': 13,
        'Nob Hill': 8,
        'Bayview': 22,
    },
    'Nob Hill': {
        'Embarcadero': 9,
        'Richmond District': 14,
        'Union Square': 7,
        'Financial District': 9,
        'Pacific Heights': 8,
        'Bayview': 19,
    },
    'Bayview': {
        'Embarcadero': 19,
        'Richmond District': 25,
        'Union Square': 17,
        'Financial District': 19,
        'Pacific Heights': 23,
        'Nob Hill': 20,
    },
}

# Define friends data (name, location, available_start, available_end, required_duration)
friends_data = [
    ('Kenneth', 'Richmond District', 1290, 1320, 30),
    ('Lisa', 'Union Square', 540, 990, 45),
    ('Joshua', 'Financial District', 720, 915, 15),
    ('Nancy', 'Pacific Heights', 480, 690, 90),
    ('Andrew', 'Nob Hill', 690, 1215, 60),
    ('John', 'Bayview', 1005, 1290, 75),
]

# Initialize Z3 solver
s = Optimize()

# Create variables for each friend
friends = []
for name, loc, start_t, end_t, dur in friends_data:
    visited = Bool(f'visited_{name}')
    start = Int(f'start_{name}')
    end = Int(f'end_{name}')
    friends.append({
        'name': name,
        'location': loc,
        'start_t': start_t,
        'end_t': end_t,
        'dur': dur,
        'visited': visited,
        'start': start,
        'end': end,
    })

# Add constraints for each friend
for f in friends:
    # If visited, start >= available start and end <= available end
    s.add(Implies(f['visited'], And(f['start'] >= f['start_t'], f['end'] <= f['end_t'])))
    # If visited, duration >= required
    s.add(Implies(f['visited'], f['end'] - f['start'] >= f['dur']))

# Add pairwise constraints for ordering and travel time
for i in range(len(friends)):
    for j in range(i+1, len(friends)):
        f1 = friends[i]
        f2 = friends[j]
        loc1 = f1['location']
        loc2 = f2['location']
        t12 = travel_time[loc1][loc2]
        t21 = travel_time[loc2][loc1]
        # If both are visited, one must come after the other with travel time
        s.add(Implies(And(f1['visited'], f2['visited']),
                      Or(f1['end'] + t12 <= f2['start'],
                         f2['end'] + t21 <= f1['start'])))

# Add initial constraints (starting from Embarcadero)
for f in friends:
    loc = f['location']
    initial_start = 540 + travel_time['Embarcadero'][loc]
    # Either start after initial travel or after another friend
    other_conds = []
    for other in friends:
        if other['name'] == f['name']:
            continue
        other_loc = other['location']
        travel_other = travel_time[other_loc][loc]
        other_conds.append(And(other['visited'], other['end'] + travel_other <= f['start']))
    s.add(Implies(f['visited'], Or(f['start'] >= initial_start, Or(other_conds))))

# Maximize the number of visited friends
sum_visited = Sum([If(f['visited'], 1, 0) for f in friends])
s.maximize(sum_visited)

# Solve and print results
if s.check() == sat:
    model = s.model()
    print("Optimal schedule:")
    schedule = []
    for f in friends:
        if model.evaluate(f['visited']):
            start = model.evaluate(f['start'])
            end = model.evaluate(f['end'])
            schedule.append( (start.as_long(), end.as_long(), f['name']) )
    # Sort by start time
    schedule.sort()
    for sched in schedule:
        start_min = sched[0]
        end_min = sched[1]
        name = sched[2]
        start_hr = start_min // 60
        start_min = start_min % 60
        end_hr = end_min // 60
        end_min = end_min % 60
        print(f"{name}: {start_hr:02}:{start_min:02} - {end_hr:02}:{end_min:02}")
else:
    print("No solution found")