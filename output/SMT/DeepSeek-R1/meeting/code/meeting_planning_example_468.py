from z3 import *

# Define travel times between locations
travel_time = {
    'The Castro': {
        'Bayview': 19,
        'Pacific Heights': 16,
        'Alamo Square': 8,
        'Fisherman\'s Wharf': 24,
        'Golden Gate Park': 11
    },
    'Bayview': {
        'The Castro': 20,
        'Pacific Heights': 23,
        'Alamo Square': 16,
        'Fisherman\'s Wharf': 25,
        'Golden Gate Park': 22
    },
    'Pacific Heights': {
        'The Castro': 16,
        'Bayview': 22,
        'Alamo Square': 10,
        'Fisherman\'s Wharf': 13,
        'Golden Gate Park': 15
    },
    'Alamo Square': {
        'The Castro': 8,
        'Bayview': 16,
        'Pacific Heights': 10,
        'Fisherman\'s Wharf': 19,
        'Golden Gate Park': 9
    },
    'Fisherman\'s Wharf': {
        'The Castro': 26,
        'Bayview': 26,
        'Pacific Heights': 12,
        'Alamo Square': 20,
        'Golden Gate Park': 25
    },
    'Golden Gate Park': {
        'The Castro': 13,
        'Bayview': 23,
        'Pacific Heights': 16,
        'Alamo Square': 10,
        'Fisherman\'s Wharf': 24
    }
}

# Friend data: (name, location, available_start, available_end, required_duration)
friends_data = [
    ('Rebecca', 'Bayview', 540, 765, 90),    # 9:00AM-12:45PM
    ('Amanda', 'Pacific Heights', 1170, 1305, 90),  # 6:30PM-9:45PM
    ('James', 'Alamo Square', 585, 1230, 90), # 9:45AM-9:15PM
    ('Sarah', 'Fisherman\'s Wharf', 480, 1290, 90), # 8:00AM-9:30PM
    ('Melissa', 'Golden Gate Park', 540, 1125, 90)  # 9:00AM-6:45PM
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
                        f2['end'] + t21 <= f1['start']))

# Initial constraint: Start at The Castro at 9:00AM (540 minutes)
for f in friends:
    loc = f['location']
    initial_arrival = 540 + travel_time['The Castro'][loc]
    # Allow visits to be either first or after other friends with travel time
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