from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Locations
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
        [0, 17, 23, 15, 7, 5, 12],    # Haight-Ashbury
        [17, 0, 7, 5, 21, 15, 7],     # Russian Hill
        [23, 7, 0, 11, 25, 20, 12],    # Fisherman's Wharf
        [15, 5, 11, 0, 17, 11, 8],     # Nob Hill
        [7, 21, 24, 20, 0, 10, 16],    # Golden Gate Park
        [5, 13, 19, 11, 10, 0, 10],    # Alamo Square
        [12, 7, 13, 8, 15, 10, 0]      # Pacific Heights
    ]

    # Friends' availability and constraints
    friends = {
        'Stephanie': {'location': 'Russian Hill', 'start': 20*60, 'end': 20*60 + 45, 'min_duration': 15},
        'Kevin': {'location': 'Fisherman\'s Wharf', 'start': 19*60 + 15, 'end': 21*60 + 45, 'min_duration': 75},
        'Robert': {'location': 'Nob Hill', 'start': 7*60 + 45, 'end': 10*60 + 30, 'min_duration': 90},
        'Steven': {'location': 'Golden Gate Park', 'start': 8*60 + 30, 'end': 17*60, 'min_duration': 75},
        'Anthony': {'location': 'Alamo Square', 'start': 7*60 + 45, 'end': 19*60 + 45, 'min_duration': 15},
        'Sandra': {'location': 'Pacific Heights', 'start': 14*60 + 45, 'end': 21*60 + 45, 'min_duration': 45}
    }

    # Variables for each friend: start and end times (in minutes since midnight)
    friend_vars = {}
    for name in friends:
        friend_vars[name] = {
            'start': Int(f'start_{name}'),
            'end': Int(f'end_{name}'),
            'met': Bool(f'met_{name}')
        }

    # Arrival time at Haight-Ashbury
    arrival_time = 9 * 60  # 9:00 AM in minutes

    # Constraints for each friend
    for name in friends:
        data = friends[name]
        loc = locations[data['location']]
        start = data['start']
        end = data['end']
        min_duration = data['min_duration']
        vars = friend_vars[name]

        # If meeting the friend, their start and end times must be within their availability
        s.add(Implies(vars['met'], And(vars['start'] >= start, vars['end'] <= end, vars['end'] - vars['start'] >= min_duration)))

    # Order constraints and travel times
    # We'll use a sequence variable to represent the order
    # For simplicity, we'll assume a fixed order and adjust constraints accordingly
    # Alternatively, we can use a more sophisticated approach with auxiliary variables

    # We'll prioritize friends with tighter time windows first
    order = ['Robert', 'Steven', 'Anthony', 'Sandra', 'Kevin', 'Stephanie']

    # Variables to track current location and time
    current_time = Int('current_time')
    current_loc = Int('current_loc')
    s.add(current_time == arrival_time)
    s.add(current_loc == locations['Haight-Ashbury'])

    # Track which friends are met
    met_friends = []
    for name in order:
        vars = friend_vars[name]
        loc = locations[friends[name]['location']]
        travel_time = Int(f'travel_time_{name}')
        
        # Define travel_time based on current_loc and loc
        s.add(travel_time == If(current_loc == 0, travel_times[0][loc],
                              If(current_loc == 1, travel_times[1][loc],
                              If(current_loc == 2, travel_times[2][loc],
                              If(current_loc == 3, travel_times[3][loc],
                              If(current_loc == 4, travel_times[4][loc],
                              If(current_loc == 5, travel_times[5][loc],
                              travel_times[6][loc]))))))

        # If meeting this friend, update current time and location
        s.add(Implies(vars['met'], And(
            vars['start'] >= current_time + travel_time,
            current_time == vars['end'],
            current_loc == loc
        )))

        # Add to met_friends if met
        met_friends.append(If(vars['met'], 1, 0))

    # Constraint: exactly 5 friends must be met
    s.add(sum(met_friends) == 5)

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        print("Optimal schedule:")
        for name in order:
            vars = friend_vars[name]
            if m.evaluate(vars['met']):
                start = m.evaluate(vars['start'])
                end = m.evaluate(vars['end'])
                start_hr = start.as_long() // 60
                start_min = start.as_long() % 60
                end_hr = end.as_long() // 60
                end_min = end.as_long() % 60
                print(f"Meet {name} at {friends[name]['location']} from {start_hr}:{start_min:02d} to {end_hr}:{end_min:02d}")
        print(f"Total friends met: {m.evaluate(sum(met_friends))}")
    else:
        print("No feasible schedule found.")

solve_scheduling()