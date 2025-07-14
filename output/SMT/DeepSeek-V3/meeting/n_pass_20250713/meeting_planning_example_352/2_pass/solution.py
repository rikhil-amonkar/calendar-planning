from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Optimize()

    # Define the locations and their indices
    locations = {
        'Union Square': 0,
        'Nob Hill': 1,
        'Haight-Ashbury': 2,
        'Chinatown': 3,
        'Marina District': 4
    }

    # Travel times matrix (in minutes)
    travel_times = [
        [0, 9, 18, 7, 18],    # Union Square to others
        [7, 0, 13, 6, 11],    # Nob Hill to others
        [17, 15, 0, 19, 17],   # Haight-Ashbury to others
        [7, 8, 19, 0, 12],     # Chinatown to others
        [16, 12, 16, 16, 0]    # Marina District to others
    ]

    # Friends' data: name, location, start time (minutes from 9:00AM), end time, min duration
    friends = [
        ('Karen', 'Nob Hill', 21*60 + 15 - 9*60, 21*60 + 45 - 9*60, 30),
        ('Joseph', 'Haight-Ashbury', 12*60 + 30 - 9*60, 19*60 + 45 - 9*60, 90),
        ('Sandra', 'Chinatown', 7*60 + 15 - 9*60, 19*60 + 15 - 9*60, 75),
        ('Nancy', 'Marina District', 11*60 + 0 - 9*60, 20*60 + 15 - 9*60, 105)
    ]

    # Variables for each friend: start time and end time of meeting
    start_vars = [Int(f'start_{name}') for name, _, _, _, _ in friends]
    end_vars = [Int(f'end_{name}') for name, _, _, _, _ in friends]
    meet_vars = [Bool(f'meet_{name}') for name, _, _, _, _ in friends]  # Whether to meet the friend

    # Constraints for each friend
    for i, (name, loc, friend_start, friend_end, min_dur) in enumerate(friends):
        s.add(Implies(meet_vars[i], start_vars[i] >= friend_start))
        s.add(Implies(meet_vars[i], end_vars[i] <= friend_end))
        s.add(Implies(meet_vars[i], end_vars[i] - start_vars[i] >= min_dur))

    # Initial position: Union Square at time 0 (9:00AM)
    current_location = locations['Union Square']
    current_time = 0

    # We must meet all four friends
    for i in range(len(friends)):
        s.add(meet_vars[i] == True)

    # Order of meetings: we'll let the solver decide the best order
    # We'll use a list to represent the order of meetings
    order = [Int(f'order_{i}') for i in range(len(friends))]
    # Each order variable must be between 0 and 3 (since there are 4 friends)
    for o in order:
        s.add(o >= 0)
        s.add(o < len(friends))
    # All order variables must be distinct
    s.add(Distinct(order))

    # Variables to track the current location and time after each meeting
    loc_vars = [Int(f'loc_{i}') for i in range(len(friends) + 1)]
    time_vars = [Int(f'time_{i}') for i in range(len(friends) + 1)]
    # Initial location and time
    s.add(loc_vars[0] == locations['Union Square'])
    s.add(time_vars[0] == 0)

    # Constraints for each meeting in the order
    for i in range(len(friends)):
        # The friend being met at this step
        friend_idx = order[i]
        name, loc, _, _, _ = friends[friend_idx]
        loc_idx = locations[loc]
        # Travel time from previous location to current friend's location
        travel_time = Int(f'travel_{i}')
        s.add(travel_time == travel_times[loc_vars[i]][loc_idx])
        # Start time must be >= previous time + travel time
        s.add(start_vars[friend_idx] >= time_vars[i] + travel_time)
        # Update location and time after meeting
        s.add(loc_vars[i+1] == loc_idx)
        s.add(time_vars[i+1] == end_vars[friend_idx])

    # Objective: minimize the total time spent (optional)
    s.minimize(time_vars[-1])

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        print("Optimal Schedule:")
        # Determine the order of meetings
        meeting_order = [m.evaluate(o).as_long() for o in order]
        for i in meeting_order:
            name, loc, _, _, _ = friends[i]
            start = m.evaluate(start_vars[i]).as_long()
            end = m.evaluate(end_vars[i]).as_long()
            start_h = 9 + start // 60
            start_m = start % 60
            end_h = 9 + end // 60
            end_m = end % 60
            print(f"Meet {name} at {loc} from {start_h:02d}:{start_m:02d} to {end_h:02d}:{end_m:02d}")
        print("All four friends met successfully!")
    else:
        print("No feasible schedule found.")

solve_scheduling()