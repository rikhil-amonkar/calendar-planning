from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Location indices
    locations = {
        'Union Square': 0,
        'Nob Hill': 1,
        'Haight-Ashbury': 2,
        'Chinatown': 3,
        'Marina District': 4
    }

    # Travel times matrix (minutes)
    travel_times = [
        [0, 9, 18, 7, 18],    # Union Square
        [7, 0, 13, 6, 11],     # Nob Hill
        [17, 15, 0, 19, 17],   # Haight-Ashbury
        [7, 8, 19, 0, 12],     # Chinatown
        [16, 12, 16, 16, 0]    # Marina District
    ]

    # Friends data with availability windows
    friends = [
        {'name': 'Karen', 'loc': 'Nob Hill', 'start': 21*60+15, 'end': 21*60+45, 'dur': 30},
        {'name': 'Joseph', 'loc': 'Haight-Ashbury', 'start': 12*60+30, 'end': 19*60+45, 'dur': 90},
        {'name': 'Sandra', 'loc': 'Chinatown', 'start': 7*60+15, 'end': 19*60+15, 'dur': 75},
        {'name': 'Nancy', 'loc': 'Marina District', 'start': 11*60+0, 'end': 20*60+15, 'dur': 105}
    ]

    # Create variables
    starts = [Int(f'start_{f["name"]}') for f in friends]
    ends = [Int(f'end_{f["name"]}') for f in friends]
    met = [Bool(f'met_{f["name"]}') for f in friends]  # Whether we meet each friend

    # Current time starts at 9:00 AM (540 minutes)
    current_time = 540
    current_loc = 'Union Square'

    # Add constraints
    for i, friend in enumerate(friends):
        # If meeting this friend, must be within their window
        s.add(Implies(met[i], starts[i] >= friend['start']))
        s.add(Implies(met[i], ends[i] <= friend['end']))
        s.add(Implies(met[i], ends[i] == starts[i] + friend['dur']))
        
        # First meeting must account for travel from Union Square
        travel_time = travel_times[locations[current_loc]][locations[friend['loc']]]
        s.add(Implies(met[i], starts[i] >= current_time + travel_time))

    # No overlapping meetings with travel time
    for i in range(len(friends)):
        for j in range(i+1, len(friends)):
            # Travel times between locations
            t_ij = travel_times[locations[friends[i]['loc']]][locations[friends[j]['loc']]]
            t_ji = travel_times[locations[friends[j]['loc']]][locations[friends[i]['loc']]]
            
            # Either i before j or j before i with travel time
            s.add(Implies(And(met[i], met[j]),
                        Or(ends[i] + t_ij <= starts[j],
                           ends[j] + t_ji <= starts[i])))

    # Maximize number of friends met
    s.maximize(Sum([If(m, 1, 0) for m in met]))

    if s.check() == sat:
        model = s.model()
        schedule = []
        for i, friend in enumerate(friends):
            if is_true(model[met[i]]):
                start = model[starts[i]].as_long()
                end = model[ends[i]].as_long()
                schedule.append({
                    'friend': friend['name'],
                    'location': friend['loc'],
                    'start': f"{start//60}:{start%60:02d}",
                    'end': f"{end//60}:{end%60:02d}"
                })
        # Sort by start time
        schedule.sort(key=lambda x: int(x['start'].split(':')[0])*60 + int(x['start'].split(':')[1]))
        return schedule
    else:
        return None

# Solve and print
print("SOLUTION:")
schedule = solve_scheduling()
if schedule:
    for meeting in schedule:
        print(f"Meet {meeting['friend']} at {meeting['location']} from {meeting['start']} to {meeting['end']}")
else:
    print("No valid schedule found that meets all constraints.")