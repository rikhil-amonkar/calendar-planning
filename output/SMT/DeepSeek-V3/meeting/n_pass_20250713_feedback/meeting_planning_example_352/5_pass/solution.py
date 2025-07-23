from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Optimize()

    # Define locations and their indices
    locations = ['Union Square', 'Nob Hill', 'Haight-Ashbury', 'Chinatown', 'Marina District']
    loc_indices = {loc: idx for idx, loc in enumerate(locations)}

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

    # We must meet all four friends
    for i, (name, loc, friend_start, friend_end, min_dur) in enumerate(friends):
        s.add(start_vars[i] >= friend_start)
        s.add(end_vars[i] <= friend_end)
        s.add(end_vars[i] - start_vars[i] >= min_dur)

    # Variables to track the order of meetings
    order = [Int(f'order_{i}') for i in range(4)]
    # Each order variable must be between 0 and 3 (since there are 4 friends)
    for o in order:
        s.add(o >= 0)
        s.add(o < 4)
    # All order variables must be distinct
    s.add(Distinct(order))

    # Variables to track the current location and time after each meeting
    loc_vars = [Int(f'loc_{i}') for i in range(5)]  # 4 meetings + initial location
    time_vars = [Int(f'time_{i}') for i in range(5)]
    
    # Initial location and time
    s.add(loc_vars[0] == loc_indices['Union Square'])
    s.add(time_vars[0] == 0)

    # Constraints for each meeting in the order
    for i in range(4):
        current_friend = order[i]
        
        # Create variables for the friend's start and end times
        friend_start = Int(f'friend_start_{i}')
        friend_end = Int(f'friend_end_{i}')
        
        # Create a variable for the friend's location index
        friend_loc = Int(f'friend_loc_{i}')
        
        # Connect the friend index to their properties
        for j, (name, loc, f_start, f_end, _) in enumerate(friends):
            s.add(Implies(current_friend == j, And(
                friend_start == start_vars[j],
                friend_end == end_vars[j],
                friend_loc == loc_indices[loc]
            )))
        
        # Travel time from previous location to current friend's location
        travel_time = Int(f'travel_{i}')
        
        # Model travel time as a lookup in the travel_times matrix
        # We create a disjunction of all possible location pairs
        travel_constraints = []
        for prev_loc in range(5):
            for curr_loc in range(5):
                travel_constraints.append(And(
                    loc_vars[i] == prev_loc,
                    friend_loc == curr_loc,
                    travel_time == travel_times[prev_loc][curr_loc]
                ))
        s.add(Or(travel_constraints))
        
        # Start time must be >= previous time + travel time
        s.add(friend_start >= time_vars[i] + travel_time)
        
        # Update location and time after meeting
        s.add(loc_vars[i+1] == friend_loc)
        s.add(time_vars[i+1] == friend_end)

    # Objective: minimize the total time spent
    s.minimize(time_vars[4])

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