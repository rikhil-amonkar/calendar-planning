from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Optimize()

    # Define the locations
    locations = ['Bayview', 'North Beach', 'Presidio', 'Haight-Ashbury', 'Union Square']
    location_indices = {loc: idx for idx, loc in enumerate(locations)}

    # Travel times matrix (in minutes)
    travel_times = [
        [0, 21, 31, 19, 17],    # Bayview to others
        [22, 0, 17, 18, 7],      # North Beach to others
        [31, 18, 0, 15, 22],     # Presidio to others
        [18, 19, 15, 0, 17],     # Haight-Ashbury to others
        [15, 10, 24, 18, 0]      # Union Square to others
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

    # Variables to represent the order of meetings (1st, 2nd, 3rd, 4th)
    meeting_order = {name: Int(f'order_{name}') for name in friends}
    for name in friends:
        s.add(And(meeting_order[name] >= 1, meeting_order[name] <= 4))

    # All meetings have distinct orders
    s.add(Distinct([meeting_order[name] for name in friends]))

    # Initial constraints: arrival at Bayview at 9:00 AM (540 minutes)
    current_time = 540  # 9:00 AM in minutes
    current_location = 'Bayview'

    # Constraints for each friend
    for name in friends:
        info = friends[name]
        # Meeting must fit within friend's availability
        s.add(And(
            meeting_start[name] >= info['start'],
            meeting_end[name] <= info['end'],
            meeting_end[name] - meeting_start[name] >= info['min_duration']
        ))

    # Constraints for travel between meetings
    for name1 in friends:
        for name2 in friends:
            if name1 != name2:
                # If name1 comes before name2 in order
                cond = meeting_order[name1] < meeting_order[name2]
                loc1 = friends[name1]['location']
                loc2 = friends[name2]['location']
                travel = travel_times[location_indices[loc1]][location_indices[loc2]]
                s.add(Implies(cond, meeting_end[name1] + travel <= meeting_start[name2]))

    # First meeting must be reachable from Bayview
    for name in friends:
        travel = travel_times[location_indices['Bayview']][location_indices[friends[name]['location']]]
        s.add(Implies(meeting_order[name] == 1, meeting_start[name] >= current_time + travel))

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        # Get the meeting order
        ordered_meetings = sorted(friends.keys(), key=lambda x: m.evaluate(meeting_order[x]).as_long())
        
        # Print the schedule
        print("SOLUTION:")
        for name in ordered_meetings:
            start = m.evaluate(meeting_start[name]).as_long()
            end = m.evaluate(meeting_end[name]).as_long()
            print(f"Meet {name} at {friends[name]['location']} from {start//60}:{start%60:02d} to {end//60}:{end%60:02d}")
    else:
        print("No solution found - cannot meet all four friends with given constraints")

solve_scheduling()