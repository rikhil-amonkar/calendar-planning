from z3 import *

# Define travel times between locations
travel_time = {
    'Sunset District': {
        'Russian Hill': 24,
        'The Castro': 17,
        'Richmond District': 12,
        'Marina District': 21,
        'North Beach': 29,
        'Union Square': 30,
        'Golden Gate Park': 11
    },
    'Russian Hill': {
        'Sunset District': 23,
        'The Castro': 21,
        'Richmond District': 14,
        'Marina District': 7,
        'North Beach': 5,
        'Union Square': 11,
        'Golden Gate Park': 21
    },
    'The Castro': {
        'Sunset District': 17,
        'Russian Hill': 18,
        'Richmond District': 16,
        'Marina District': 21,
        'North Beach': 20,
        'Union Square': 19,
        'Golden Gate Park': 11
    },
    'Richmond District': {
        'Sunset District': 11,
        'Russian Hill': 13,
        'The Castro': 16,
        'Marina District': 9,
        'North Beach': 17,
        'Union Square': 21,
        'Golden Gate Park': 9
    },
    'Marina District': {
        'Sunset District': 19,
        'Russian Hill': 8,
        'The Castro': 22,
        'Richmond District': 11,
        'North Beach': 11,
        'Union Square': 16,
        'Golden Gate Park': 18
    },
    'North Beach': {
        'Sunset District': 27,
        'Russian Hill': 4,
        'The Castro': 22,
        'Richmond District': 18,
        'Marina District': 9,
        'Union Square': 7,
        'Golden Gate Park': 22
    },
    'Union Square': {
        'Sunset District': 26,
        'Russian Hill': 13,
        'The Castro': 19,
        'Richmond District': 20,
        'Marina District': 18,
        'North Beach': 10,
        'Golden Gate Park': 22
    },
    'Golden Gate Park': {
        'Sunset District': 10,
        'Russian Hill': 19,
        'The Castro': 13,
        'Richmond District': 7,
        'Marina District': 16,
        'North Beach': 24,
        'Union Square': 22
    }
}

# Friend data: (name, location, available_start, available_end, required_duration)
friends_data = [
    ('Karen', 'Russian Hill', 1245, 1305, 60),
    ('Jessica', 'The Castro', 945, 1170, 60),
    ('Matthew', 'Richmond District', 450, 915, 15),
    ('Michelle', 'Marina District', 630, 1065, 75),
    ('Carol', 'North Beach', 720, 1020, 90),
    ('Stephanie', 'Union Square', 645, 855, 30),
    ('Linda', 'Golden Gate Park', 645, 1320, 90)
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
    # If visited, ensure time within availability and duration
    s.add(Implies(f['visited'], And(f['start'] >= f['start_t'], f['end'] <= f['end_t'])))
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
        # Either f1 comes before f2 with travel time or vice versa
        s.add(Implies(And(f1['visited'], f2['visited']),
                      Or(f1['end'] + t12 <= f2['start'],
                         f2['end'] + t21 <= f1['start'])))

# Initial constraint: Start at Sunset District at 9:00AM (540 minutes)
for f in friends:
    loc = f['location']
    initial_arrival = 540 + travel_time['Sunset District'][loc]
    # Can only start at this friend if either:
    # 1. It's the first visit and start >= initial_arrival
    # OR
    # 2. It comes after another friend with travel time
    other_conds = []
    for other in friends:
        if other['name'] == f['name']:
            continue
        other_loc = other['location']
        travel_needed = travel_time[other_loc][loc]
        other_conds.append(And(other['visited'], other['end'] + travel_needed <= f['start']))
    s.add(Implies(f['visited'], Or(f['start'] >= initial_arrival, Or(other_conds))))

# Maximize number of friends met
sum_visited = Sum([If(f['visited'], 1, 0) for f in friends])
s.maximize(sum_visited)

# Solve and display results
if s.check() == sat:
    model = s.model()
    print("Optimal schedule:")
    schedule = []
    for f in friends:
        if model.evaluate(f['visited']):
            start_val = model.evaluate(f['start']).as_long()
            end_val = model.evaluate(f['end']).as_long()
            schedule.append((start_val, end_val, f['name']))
    # Sort by start time
    schedule.sort()
    for sched in schedule:
        start_hr = sched[0] // 60
        start_min = sched[0] % 60
        end_hr = sched[1] // 60
        end_min = sched[1] % 60
        print(f"{sched[2]}: {start_hr:02}:{start_min:02} - {end_hr:02}:{end_min:02}")
else:
    print("No solution found")