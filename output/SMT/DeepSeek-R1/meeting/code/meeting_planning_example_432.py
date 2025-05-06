from z3 import *

# Define travel times between locations
travel_time = {
    'Golden Gate Park': {
        'Fisherman\'s Wharf': 24,
        'Bayview': 23,
        'Mission District': 17,
        'Embarcadero': 25,
        'Financial District': 26
    },
    'Fisherman\'s Wharf': {
        'Golden Gate Park': 25,
        'Bayview': 26,
        'Mission District': 22,
        'Embarcadero': 8,
        'Financial District': 11
    },
    'Bayview': {
        'Golden Gate Park': 22,
        'Fisherman\'s Wharf': 25,
        'Mission District': 13,
        'Embarcadero': 19,
        'Financial District': 19
    },
    'Mission District': {
        'Golden Gate Park': 17,
        'Fisherman\'s Wharf': 22,
        'Bayview': 15,
        'Embarcadero': 19,
        'Financial District': 17
    },
    'Embarcadero': {
        'Golden Gate Park': 25,
        'Fisherman\'s Wharf': 6,
        'Bayview': 21,
        'Mission District': 20,
        'Financial District': 5
    },
    'Financial District': {
        'Golden Gate Park': 23,
        'Fisherman\'s Wharf': 10,
        'Bayview': 19,
        'Mission District': 17,
        'Embarcadero': 4
    }
}

# Friend data: (name, location, available_start, available_end, required_duration)
friends_data = [
    ('Joseph', 'Fisherman\'s Wharf', 480, 1050, 90),
    ('Jeffrey', 'Bayview', 1050, 1290, 60),
    ('Kevin', 'Mission District', 675, 915, 30),
    ('David', 'Embarcadero', 495, 540, 30),
    ('Barbara', 'Financial District', 630, 990, 15)
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

# Initial constraint: Start at Golden Gate Park at 9:00AM (540 minutes)
for f in friends:
    loc = f['location']
    initial_arrival = 540 + travel_time['Golden Gate Park'][loc]
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