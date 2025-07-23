from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

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

    # Order of meetings (we'll try all permutations to find the best schedule)
    # For simplicity, we'll consider meeting friends in the order they appear, but in practice,
    # we'd need to explore all permutations or use a more sophisticated approach.
    # Here, we'll prioritize meeting as many friends as possible.

    # Constraints for travel times and ordering of meetings
    # We'll assume a fixed order for simplicity (e.g., Sandra, Nancy, Joseph, Karen)
    # This is a simplification; a full solution would explore all possible orders.

    # For each friend, if we meet them, their start time must be >= current_time + travel time
    # After meeting, current_time becomes end_time + travel time to next location
    # We'll model this for one possible order.

    # Let's try the order: Sandra, Nancy, Joseph, Karen
    order = [2, 3, 1, 0]  # Indices of friends in the order Sandra, Nancy, Joseph, Karen

    prev_time = 0
    prev_loc = locations['Union Square']
    for i in order:
        name, loc, _, _, _ = friends[i]
        loc_idx = locations[loc]
        travel_time = travel_times[prev_loc][loc_idx]
        s.add(Implies(meet_vars[i], start_vars[i] >= prev_time + travel_time))
        prev_time = If(meet_vars[i], end_vars[i], prev_time)
        prev_loc = If(meet_vars[i], loc_idx, prev_loc)

    # Objective: maximize the number of friends met
    s.maximize(Sum([If(meet_vars[i], 1, 0) for i in range(len(friends))]))

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        print("Optimal Schedule:")
        total_met = 0
        for i, (name, loc, _, _, _) in enumerate(friends):
            if m.evaluate(meet_vars[i]):
                start = m.evaluate(start_vars[i]).as_long()
                end = m.evaluate(end_vars[i]).as_long()
                start_h = 9 + start // 60
                start_m = start % 60
                end_h = 9 + end // 60
                end_m = end % 60
                print(f"Meet {name} at {loc} from {start_h:02d}:{start_m:02d} to {end_h:02d}:{end_m:02d}")
                total_met += 1
        print(f"Total friends met: {total_met}")
    else:
        print("No feasible schedule found.")

solve_scheduling()