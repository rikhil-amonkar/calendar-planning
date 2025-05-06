from z3 import *

# Define travel times between locations
travel_time = {
    'Union Square': {
        'The Castro': 17,
        'North Beach': 10,
        'Embarcadero': 11,
        'Alamo Square': 15,
        'Nob Hill': 9,
        'Presidio': 24,
        'Fisherman\'s Wharf': 15,
        'Mission District': 14,
        'Haight-Ashbury': 18
    },
    'The Castro': {
        'Union Square': 19,
        'North Beach': 20,
        'Embarcadero': 22,
        'Alamo Square': 8,
        'Nob Hill': 16,
        'Presidio': 20,
        'Fisherman\'s Wharf': 24,
        'Mission District': 7,
        'Haight-Ashbury': 6
    },
    'North Beach': {
        'Union Square': 7,
        'The Castro': 23,
        'Embarcadero': 6,
        'Alamo Square': 16,
        'Nob Hill': 7,
        'Presidio': 17,
        'Fisherman\'s Wharf': 5,
        'Mission District': 18,
        'Haight-Ashbury': 18
    },
    'Embarcadero': {
        'Union Square': 10,
        'The Castro': 25,
        'North Beach': 5,
        'Alamo Square': 19,
        'Nob Hill': 10,
        'Presidio': 20,
        'Fisherman\'s Wharf': 6,
        'Mission District': 20,
        'Haight-Ashbury': 21
    },
    'Alamo Square': {
        'Union Square': 14,
        'The Castro': 8,
        'North Beach': 15,
        'Embarcadero': 16,
        'Nob Hill': 11,
        'Presidio': 17,
        'Fisherman\'s Wharf': 19,
        'Mission District': 10,
        'Haight-Ashbury': 5
    },
    'Nob Hill': {
        'Union Square': 7,
        'The Castro': 17,
        'North Beach': 8,
        'Embarcadero': 9,
        'Alamo Square': 11,
        'Presidio': 17,
        'Fisherman\'s Wharf': 10,
        'Mission District': 13,
        'Haight-Ashbury': 13
    },
    'Presidio': {
        'Union Square': 22,
        'The Castro': 21,
        'North Beach': 18,
        'Embarcadero': 20,
        'Alamo Square': 19,
        'Nob Hill': 18,
        'Fisherman\'s Wharf': 19,
        'Mission District': 26,
        'Haight-Ashbury': 15
    },
    'Fisherman\'s Wharf': {
        'Union Square': 13,
        'The Castro': 27,
        'North Beach': 6,
        'Embarcadero': 8,
        'Alamo Square': 21,
        'Nob Hill': 11,
        'Presidio': 17,
        'Mission District': 22,
        'Haight-Ashbury': 22
    },
    'Mission District': {
        'Union Square': 15,
        'The Castro': 7,
        'North Beach': 17,
        'Embarcadero': 19,
        'Alamo Square': 11,
        'Nob Hill': 12,
        'Presidio': 25,
        'Fisherman\'s Wharf': 22,
        'Haight-Ashbury': 12
    },
    'Haight-Ashbury': {
        'Union Square': 19,
        'The Castro': 6,
        'North Beach': 19,
        'Embarcadero': 20,
        'Alamo Square': 5,
        'Nob Hill': 15,
        'Presidio': 15,
        'Fisherman\'s Wharf': 23,
        'Mission District': 11
    }
}

# Friend data: (name, location, available_start, available_end, required_duration)
friends_data = [
    ('Melissa', 'The Castro', 1215, 1290, 30),
    ('Kimberly', 'North Beach', 420, 630, 15),
    ('Joseph', 'Embarcadero', 1050, 1290, 75),
    ('Barbara', 'Alamo Square', 1260, 1305, 15),
    ('Kenneth', 'Nob Hill', 735, 1035, 105),
    ('Joshua', 'Presidio', 990, 1095, 105),
    ('Brian', 'Fisherman\'s Wharf', 570, 930, 45),
    ('Steven', 'Mission District', 1170, 1260, 90),
    ('Betty', 'Haight-Ashbury', 1140, 1230, 90)
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

# Initial constraint: Start at Union Square at 9:00AM (540 minutes)
for f in friends:
    loc = f['location']
    initial_arrival = 540 + travel_time['Union Square'][loc]
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