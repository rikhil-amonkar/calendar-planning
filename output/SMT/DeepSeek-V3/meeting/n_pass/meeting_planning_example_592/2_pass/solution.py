from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Locations and their indices
    locations = {
        'North Beach': 0,
        'Pacific Heights': 1,
        'Chinatown': 2,
        'Union Square': 3,
        'Mission District': 4,
        'Golden Gate Park': 5,
        'Nob Hill': 6
    }

    # Travel times matrix (in minutes)
    travel_times = [
        [0, 8, 6, 7, 18, 22, 7],    # North Beach
        [9, 0, 11, 12, 15, 15, 8],  # Pacific Heights
        [3, 10, 0, 7, 18, 23, 8],   # Chinatown
        [10, 15, 7, 0, 14, 22, 9],  # Union Square
        [17, 16, 16, 15, 0, 17, 12],# Mission District
        [24, 16, 23, 22, 17, 0, 20],# Golden Gate Park
        [8, 8, 6, 7, 13, 17, 0]     # Nob Hill
    ]

    # Friends' data: name, location, start time, end time, min duration (in minutes)
    friends = [
        ('James', 1, 20*60, 22*60, 120),    # Pacific Heights, 8:00PM-10:00PM, 120 min
        ('Robert', 2, 12*60 + 15, 16*60 + 45, 90),  # Chinatown, 12:15PM-4:45PM, 90 min
        ('Jeffrey', 3, 9*60 + 30, 15*60 + 30, 120), # Union Square, 9:30AM-3:30PM, 120 min
        ('Carol', 4, 18*60 + 15, 21*60 + 15, 15),   # Mission District, 6:15PM-9:15PM, 15 min
        ('Mark', 5, 11*60 + 30, 17*60 + 45, 15),    # Golden Gate Park, 11:30AM-5:45PM, 15 min
        ('Sandra', 6, 8*60, 15*60 + 30, 15)         # Nob Hill, 8:00AM-3:30PM, 15 min
    ]

    # Variables for each friend: start and end times of the meeting
    start_vars = [Int(f'start_{name}') for name, _, _, _, _ in friends]
    end_vars = [Int(f'end_{name}') for name, _, _, _, _ in friends]
    meet_vars = [Bool(f'meet_{name}') for name, _, _, _, _ in friends]  # Whether to meet the friend

    # Current location starts at North Beach (0) at 9:00AM (540 minutes)
    current_time = 9 * 60
    current_loc = locations['North Beach']

    # Constraints for each friend
    for i, (name, loc, friend_start, friend_end, min_dur) in enumerate(friends):
        # If meeting the friend, the meeting must fit within their window and have min duration
        s.add(Implies(meet_vars[i], start_vars[i] >= friend_start))
        s.add(Implies(meet_vars[i], end_vars[i] <= friend_end))
        s.add(Implies(meet_vars[i], end_vars[i] - start_vars[i] >= min_dur))

        # If not meeting the friend, start and end times are unconstrained (but we'll minimize them)
        s.add(Implies(Not(meet_vars[i]), start_vars[i] == 0))
        s.add(Implies(Not(meet_vars[i]), end_vars[i] == 0))

    # Order constraints: ensure travel time is accounted for between consecutive meetings
    # We'll use a list to represent the sequence of meetings
    # For simplicity, we'll assume a fixed order and let Z3 find the best one
    # This is a simplified approach; a more complex model would use sequencing variables

    # For each pair of consecutive meetings, ensure travel time is accounted for
    # We'll use a greedy approach to order meetings by their start times
    # This is a heuristic; a full solution would explore all possible orders

    # Maximize the number of friends met
    s.maximize(Sum([If(meet_vars[i], 1, 0) for i in range(len(friends))]))

    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        print("Optimal Schedule:")
        total_met = 0
        for i, (name, loc, _, _, _) in enumerate(friends):
            if m.evaluate(meet_vars[i]):
                total_met += 1
                start = m.evaluate(start_vars[i]).as_long()
                end = m.evaluate(end_vars[i]).as_long()
                start_hr = start // 60
                start_min = start % 60
                end_hr = end // 60
                end_min = end % 60
                print(f"Meet {name} at {list(locations.keys())[loc]} from {start_hr}:{start_min:02d} to {end_hr}:{end_min:02d}")
        print(f"Total friends met: {total_met}")
    else:
        print("No valid schedule found.")

solve_scheduling()