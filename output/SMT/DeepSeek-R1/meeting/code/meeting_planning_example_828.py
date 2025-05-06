from z3 import *

# Define travel times between locations
travel_time = {
    'Marina District': {
        'Richmond District': 11,
        'Union Square': 16,
        'Nob Hill': 12,
        'Fisherman\'s Wharf': 10,
        'Golden Gate Park': 18,
        'Embarcadero': 14,
        'Financial District': 17,
        'North Beach': 11,
        'Presidio': 10
    },
    'Richmond District': {
        'Marina District': 9,
        'Union Square': 21,
        'Nob Hill': 17,
        'Fisherman\'s Wharf': 18,
        'Golden Gate Park': 9,
        'Embarcadero': 19,
        'Financial District': 22,
        'North Beach': 17,
        'Presidio': 7
    },
    'Union Square': {
        'Marina District': 18,
        'Richmond District': 20,
        'Nob Hill': 9,
        'Fisherman\'s Wharf': 15,
        'Golden Gate Park': 22,
        'Embarcadero': 11,
        'Financial District': 9,
        'North Beach': 10,
        'Presidio': 24
    },
    'Nob Hill': {
        'Marina District': 11,
        'Richmond District': 14,
        'Union Square': 7,
        'Fisherman\'s Wharf': 10,
        'Golden Gate Park': 17,
        'Embarcadero': 9,
        'Financial District': 9,
        'North Beach': 8,
        'Presidio': 17
    },
    'Fisherman\'s Wharf': {
        'Marina District': 9,
        'Richmond District': 18,
        'Union Square': 13,
        'Nob Hill': 11,
        'Golden Gate Park': 25,
        'Embarcadero': 8,
        'Financial District': 11,
        'North Beach': 6,
        'Presidio': 17
    },
    'Golden Gate Park': {
        'Marina District': 16,
        'Richmond District': 7,
        'Union Square': 22,
        'Nob Hill': 20,
        'Fisherman\'s Wharf': 24,
        'Embarcadero': 25,
        'Financial District': 26,
        'North Beach': 23,
        'Presidio': 11
    },
    'Embarcadero': {
        'Marina District': 12,
        'Richmond District': 21,
        'Union Square': 10,
        'Nob Hill': 10,
        'Fisherman\'s Wharf': 6,
        'Golden Gate Park': 25,
        'Financial District': 5,
        'North Beach': 5,
        'Presidio': 20
    },
    'Financial District': {
        'Marina District': 15,
        'Richmond District': 21,
        'Union Square': 9,
        'Nob Hill': 8,
        'Fisherman\'s Wharf': 10,
        'Golden Gate Park': 23,
        'Embarcadero': 4,
        'North Beach': 7,
        'Presidio': 22
    },
    'North Beach': {
        'Marina District': 9,
        'Richmond District': 18,
        'Union Square': 7,
        'Nob Hill': 7,
        'Fisherman\'s Wharf': 5,
        'Golden Gate Park': 22,
        'Embarcadero': 6,
        'Financial District': 8,
        'Presidio': 17
    },
    'Presidio': {
        'Marina District': 11,
        'Richmond District': 7,
        'Union Square': 22,
        'Nob Hill': 18,
        'Fisherman\'s Wharf': 19,
        'Golden Gate Park': 12,
        'Embarcadero': 20,
        'Financial District': 23,
        'North Beach': 18
    }
}

# Friend data: (name, location, available_start, available_end, required_duration)
friends_data = [
    ('Stephanie', 'Richmond District', 975, 1290, 75),     # 4:15PM-9:30PM
    ('William', 'Union Square', 645, 1050, 45),            # 10:45AM-5:30PM
    ('Elizabeth', 'Nob Hill', 735, 900, 105),              # 12:15PM-3:00PM
    ('Joseph', 'Fisherman\'s Wharf', 765, 840, 75),        # 12:45PM-2:00PM
    ('Anthony', 'Golden Gate Park', 780, 1230, 75),        # 1:00PM-8:30PM
    ('Barbara', 'Embarcadero', 1155, 1230, 75),            # 7:15PM-8:30PM
    ('Carol', 'Financial District', 705, 975, 60),         # 11:45AM-4:15PM
    ('Sandra', 'North Beach', 600, 750, 15),               # 10:00AM-12:30PM
    ('Kenneth', 'Presidio', 1290, 1335, 45)                # 9:15PM-10:15PM
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

# Initial constraint: Start at Marina District at 9:00AM (540 minutes)
for f in friends:
    loc = f['location']
    initial_arrival = 540 + travel_time['Marina District'][loc]
    # Can only start at this friend if either:
    # 1. First visit: start >= initial arrival time from Marina
    # OR
    # 2. After another friend's visit with travel time
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