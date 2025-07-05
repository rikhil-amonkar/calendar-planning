from z3 import *

def solve_scheduling():
    s = Solver()

    # Locations mapping
    locations = {
        'Haight-Ashbury': 0,
        'Russian Hill': 1,
        'Fisherman\'s Wharf': 2,
        'Nob Hill': 3,
        'Golden Gate Park': 4,
        'Alamo Square': 5,
        'Pacific Heights': 6
    }

    # Travel times matrix (minutes)
    travel_times = [
        [0, 17, 23, 15, 7, 5, 12],
        [17, 0, 7, 5, 21, 15, 7],
        [23, 7, 0, 11, 25, 20, 12],
        [15, 5, 11, 0, 17, 11, 8],
        [7, 21, 24, 20, 0, 10, 16],
        [5, 13, 19, 11, 10, 0, 10],
        [12, 7, 13, 8, 15, 10, 0]
    ]

    # Friends data
    friends = {
        'Stephanie': {'location': 'Russian Hill', 'start': 20*60, 'end': 20*60 + 45, 'min_duration': 15},
        'Kevin': {'location': 'Fisherman\'s Wharf', 'start': 19*60 + 15, 'end': 21*60 + 45, 'min_duration': 75},
        'Robert': {'location': 'Nob Hill', 'start': 7*60 + 45, 'end': 10*60 + 30, 'min_duration': 90},
        'Steven': {'location': 'Golden Gate Park', 'start': 8*60 + 30, 'end': 17*60, 'min_duration': 75},
        'Anthony': {'location': 'Alamo Square', 'start': 7*60 + 45, 'end': 19*60 + 45, 'min_duration': 15},
        'Sandra': {'location': 'Pacific Heights', 'start': 14*60 + 45, 'end': 21*60 + 45, 'min_duration': 45}
    }

    # Create variables for each friend
    friend_vars = {}
    for name in friends:
        friend_vars[name] = {
            'start': Int(f'start_{name}'),
            'end': Int(f'end_{name}'),
            'met': Bool(f'met_{name}')
        }

    # Arrival time
    current_time = Int('current_time')
    current_loc = Int('current_loc')
    s.add(current_time == 9*60)  # 9:00 AM
    s.add(current_loc == locations['Haight-Ashbury'])

    # Meeting constraints
    for name in friends:
        data = friends[name]
        loc = locations[data['location']]
        vars = friend_vars[name]
        
        s.add(Implies(vars['met'], And(
            vars['start'] >= data['start'],
            vars['end'] <= data['end'],
            vars['end'] - vars['start'] >= data['min_duration']
        )))

    # Meeting order - try different permutations
    meeting_order = ['Robert', 'Steven', 'Anthony', 'Sandra', 'Kevin', 'Stephanie']
    met_friends = []

    for name in meeting_order:
        vars = friend_vars[name]
        loc = locations[friends[name]['location']]
        
        # Travel time constraint
        travel_time = Int(f'travel_{name}')
        s.add(travel_time >= 0)
        for i in range(7):
            s.add(If(current_loc == i, travel_time == travel_times[i][loc], True))

        # If meeting this friend
        s.add(Implies(vars['met'], And(
            vars['start'] >= current_time + travel_time,
            current_time == vars['end'],
            current_loc == loc
        )))

        met_friends.append(If(vars['met'], 1, 0))

    # Exactly 5 friends must be met
    s.add(sum(met_friends) == 5)

    # Try to find a solution
    if s.check() == sat:
        m = s.model()
        print("Feasible schedule found:")
        total_met = 0
        for name in meeting_order:
            if m.evaluate(friend_vars[name]['met']):
                start = m.evaluate(friend_vars[name]['start'])
                end = m.evaluate(friend_vars[name]['end'])
                print(f"Meet {name} at {friends[name]['location']} from {start.as_long()//60}:{start.as_long()%60:02d} to {end.as_long()//60}:{end.as_long()%60:02d}")
                total_met += 1
        print(f"Total friends met: {total_met}")
    else:
        print("No feasible schedule found that meets exactly 5 friends.")
        print("Try relaxing some constraints or adjusting meeting durations.")

solve_scheduling()