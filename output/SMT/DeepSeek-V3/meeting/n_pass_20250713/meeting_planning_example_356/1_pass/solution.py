from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define the locations
    locations = ['Bayview', 'North Beach', 'Presidio', 'Haight-Ashbury', 'Union Square']
    location_indices = {loc: idx for idx, loc in enumerate(locations)}

    # Travel times matrix (in minutes)
    travel_times = [
        [0, 21, 31, 19, 17],    # Bayview to others
        [22, 0, 17, 18, 7],      # North Beach to others
        [31, 18, 0, 15, 22],      # Presidio to others
        [18, 19, 15, 0, 17],      # Haight-Ashbury to others
        [15, 10, 24, 18, 0]       # Union Square to others
    ]

    # Friend constraints
    friends = {
        'Barbara': {'location': 'North Beach', 'start': 13*60 + 45, 'end': 20*60 + 15, 'min_duration': 60},
        'Margaret': {'location': 'Presidio', 'start': 10*60 + 15, 'end': 15*60 + 15, 'min_duration': 30},
        'Kevin': {'location': 'Haight-Ashbury', 'start': 20*60 + 0, 'end': 20*60 + 45, 'min_duration': 30},
        'Kimberly': {'location': 'Union Square', 'start': 7*60 + 45, 'end': 16*60 + 45, 'min_duration': 30}
    }

    # Variables for each friend: start and end times of the meeting
    meeting_start = {name: Int(f'start_{name}') for name in friends}
    meeting_end = {name: Int(f'end_{name}') for name in friends}
    meet_friend = {name: Bool(f'meet_{name}') for name in friends}  # Whether we meet the friend

    # Initial constraints: arrival at Bayview at 9:00 AM (540 minutes)
    current_time = 540  # 9:00 AM in minutes
    current_location = 'Bayview'

    # For each friend, add constraints if we decide to meet them
    for name in friends:
        info = friends[name]
        loc = info['location']
        travel_time = travel_times[location_indices[current_location]][location_indices[loc]]

        # If we meet the friend, the meeting must fit within their availability and our schedule
        s.add(Implies(meet_friend[name], And(
            meeting_start[name] >= info['start'],
            meeting_end[name] <= info['end'],
            meeting_end[name] - meeting_start[name] >= info['min_duration'],
            meeting_start[name] >= current_time + travel_time
        ))

        # Update current_time and current_location if we meet the friend
        # We need to choose which friends to meet, so this is handled by the solver
        # We'll add a constraint that the next meeting starts after the current one ends plus travel time

    # Ensure that meetings don't overlap and account for travel times
    # This is a bit tricky because the order of meetings is not fixed
    # We'll use auxiliary variables to model the order

    # For simplicity, we'll assume a specific order or use a more complex model
    # Here, we'll assume we can meet Barbara, Margaret, Kimberly, Kevin in some order
    # and add constraints accordingly

    # For example, one possible order is Margaret -> Kimberly -> Barbara -> Kevin
    # We'll let the solver decide the order

    # To model the order, we can use a permutation of the friends
    # But this is complex, so we'll instead assume that we can meet at most one friend at a time
    # and add constraints that the start time of a meeting is after the end time of the previous meeting plus travel time

    # For simplicity, we'll assume we meet all friends we can in some order
    # and let the solver find a feasible order

    # Add constraints that meetings don't overlap and travel times are accounted for
    # This is a simplified approach and may not cover all cases
    for name1 in friends:
        for name2 in friends:
            if name1 != name2:
                loc1 = friends[name1]['location']
                loc2 = friends[name2]['location']
                travel = travel_times[location_indices[loc1]][location_indices[loc2]]
                s.add(Implies(And(meet_friend[name1], meet_friend[name2]),
                              Or(meeting_end[name1] + travel <= meeting_start[name2],
                                 meeting_end[name2] + travel <= meeting_start[name1])))

    # Maximize the number of friends met
    s.maximize(Sum([If(meet_friend[name], 1, 0) for name in friends]))

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        # Print the schedule
        print("SOLUTION:")
        for name in friends:
            if m.evaluate(meet_friend[name]):
                start = m.evaluate(meeting_start[name]).as_long()
                end = m.evaluate(meeting_end[name]).as_long()
                print(f"Meet {name} at {friends[name]['location']} from {start//60}:{start%60:02d} to {end//60}:{end%60:02d}")
        print(f"Total friends met: {sum(1 for name in friends if m.evaluate(meet_friend[name]))}")
    else:
        print("No solution found")

solve_scheduling()