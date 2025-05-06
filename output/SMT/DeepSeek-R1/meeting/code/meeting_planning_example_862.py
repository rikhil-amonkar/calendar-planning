from z3 import *

# Define travel times between locations
travel_time = {
    'Mission District': {
        'Alamo Square': 11,
        'Presidio': 25,
        'Russian Hill': 15,
        'North Beach': 17,
        'Golden Gate Park': 17,
        'Richmond District': 20,
        'Embarcadero': 19,
        'Financial District': 15,
        'Marina District': 19,
    },
    'Alamo Square': {
        'Mission District': 10,
        'Presidio': 17,
        'Russian Hill': 13,
        'North Beach': 15,
        'Golden Gate Park': 9,
        'Richmond District': 11,
        'Embarcadero': 16,
        'Financial District': 17,
        'Marina District': 15,
    },
    'Presidio': {
        'Mission District': 26,
        'Alamo Square': 19,
        'Russian Hill': 14,
        'North Beach': 18,
        'Golden Gate Park': 12,
        'Richmond District': 7,
        'Embarcadero': 20,
        'Financial District': 23,
        'Marina District': 11,
    },
    'Russian Hill': {
        'Mission District': 16,
        'Alamo Square': 15,
        'Presidio': 14,
        'North Beach': 5,
        'Golden Gate Park': 21,
        'Richmond District': 14,
        'Embarcadero': 8,
        'Financial District': 11,
        'Marina District': 7,
    },
    'North Beach': {
        'Mission District': 18,
        'Alamo Square': 16,
        'Presidio': 17,
        'Russian Hill': 4,
        'Golden Gate Park': 22,
        'Richmond District': 18,
        'Embarcadero': 6,
        'Financial District': 8,
        'Marina District': 9,
    },
    'Golden Gate Park': {
        'Mission District': 17,
        'Alamo Square': 9,
        'Presidio': 11,
        'Russian Hill': 19,
        'North Beach': 23,
        'Richmond District': 7,
        'Embarcadero': 25,
        'Financial District': 26,
        'Marina District': 16,
    },
    'Richmond District': {
        'Mission District': 20,
        'Alamo Square': 13,
        'Presidio': 7,
        'Russian Hill': 13,
        'North Beach': 17,
        'Golden Gate Park': 9,
        'Embarcadero': 19,
        'Financial District': 22,
        'Marina District': 9,
    },
    'Embarcadero': {
        'Mission District': 20,
        'Alamo Square': 19,
        'Presidio': 20,
        'Russian Hill': 8,
        'North Beach': 5,
        'Golden Gate Park': 25,
        'Richmond District': 21,
        'Financial District': 5,
        'Marina District': 12,
    },
    'Financial District': {
        'Mission District': 17,
        'Alamo Square': 17,
        'Presidio': 22,
        'Russian Hill': 11,
        'North Beach': 7,
        'Golden Gate Park': 23,
        'Richmond District': 21,
        'Embarcadero': 4,
        'Marina District': 15,
    },
    'Marina District': {
        'Mission District': 20,
        'Alamo Square': 15,
        'Presidio': 10,
        'Russian Hill': 8,
        'North Beach': 11,
        'Golden Gate Park': 18,
        'Richmond District': 11,
        'Embarcadero': 14,
        'Financial District': 17,
    },
}

# Define friends data (name, location, available_start, available_end, required_duration)
friends_data = [
    ('Laura', 'Alamo Square', 870, 975, 75),
    ('Brian', 'Presidio', 615, 1020, 30),
    ('Karen', 'Russian Hill', 1080, 1215, 90),
    ('Stephanie', 'North Beach', 615, 960, 75),
    ('Helen', 'Golden Gate Park', 690, 1305, 120),
    ('Sandra', 'Richmond District', 480, 915, 30),
    ('Mary', 'Embarcadero', 1005, 1125, 120),
    ('Deborah', 'Financial District', 1140, 1245, 105),
    ('Elizabeth', 'Marina District', 510, 795, 105),
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

# Add initial constraints (starting from Mission District)
for f in friends:
    loc = f['location']
    mission_to_loc = travel_time['Mission District'][loc]
    initial_start = 540 + mission_to_loc  # 9:00 AM is 540 minutes
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
    for f in friends:
        if model.evaluate(f['visited']):
            start = model.evaluate(f['start'])
            end = model.evaluate(f['end'])
            print(f"{f['name']}: {start//60:02}:{start%60:02} - {end//60:02}:{end%60:02}")
else:
    print("No solution found")