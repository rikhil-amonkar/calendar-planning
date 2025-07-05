from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define the locations and their indices
    locations = {
        "Marina District": 0,
        "Richmond District": 1,
        "Union Square": 2,
        "Nob Hill": 3,
        "Fisherman's Wharf": 4,
        "Golden Gate Park": 5,
        "Embarcadero": 6,
        "Financial District": 7,
        "North Beach": 8,
        "Presidio": 9
    }

    # Travel times matrix (in minutes)
    travel_times = [
        [0, 11, 16, 12, 10, 18, 14, 17, 11, 10],  # Marina District
        [9, 0, 21, 17, 18, 9, 19, 22, 17, 7],     # Richmond District
        [18, 20, 0, 9, 15, 22, 11, 9, 10, 24],    # Union Square
        [11, 14, 7, 0, 10, 17, 9, 9, 8, 17],      # Nob Hill
        [9, 18, 13, 11, 0, 25, 8, 11, 6, 17],     # Fisherman's Wharf
        [16, 7, 22, 20, 24, 0, 25, 26, 23, 11],   # Golden Gate Park
        [12, 21, 10, 10, 6, 25, 0, 5, 5, 20],     # Embarcadero
        [15, 21, 9, 8, 10, 23, 4, 0, 7, 22],      # Financial District
        [9, 18, 7, 7, 5, 22, 6, 8, 0, 17],        # North Beach
        [11, 7, 22, 18, 19, 12, 20, 23, 18, 0]    # Presidio
    ]

    # Friends' data: name, location, start time, end time, min duration (in minutes)
    friends = [
        ("Stephanie", "Richmond District", 16*60 + 15, 21*60 + 30, 75),
        ("William", "Union Square", 10*60 + 45, 17*60 + 30, 45),
        ("Elizabeth", "Nob Hill", 12*60 + 15, 15*60 + 0, 105),
        ("Joseph", "Fisherman's Wharf", 12*60 + 45, 14*60 + 0, 75),
        ("Anthony", "Golden Gate Park", 13*60 + 0, 20*60 + 30, 75),
        ("Barbara", "Embarcadero", 19*60 + 15, 20*60 + 30, 75),
        ("Carol", "Financial District", 11*60 + 45, 16*60 + 15, 60),
        ("Sandra", "North Beach", 10*60 + 0, 12*60 + 30, 15),
        ("Kenneth", "Presidio", 21*60 + 15, 22*60 + 15, 45)
    ]

    # Current location starts at Marina District at 9:00 AM (540 minutes)
    current_location = locations["Marina District"]
    current_time = 9 * 60

    # Variables for each friend: start and end times of meeting
    meet_vars = []
    for i, (name, loc, friend_start, friend_end, min_duration) in enumerate(friends):
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        meet_vars.append((name, loc, friend_start, friend_end, min_duration, start, end))
        # Constraints: meeting must be within friend's availability
        s.add(start >= friend_start)
        s.add(end <= friend_end)
        s.add(end == start + min_duration)
        # Ensure meeting duration is exactly min_duration
        s.add(end - start == min_duration)

    # Order of meetings (permutation to try all possible orders)
    # We'll use a greedy approach to prioritize friends with tighter windows
    # For Z3, we need to define the order constraints
    # This is a simplified approach; a more complex model would use permutations

    # Add travel time constraints between consecutive meetings
    for i in range(len(meet_vars)):
        for j in range(len(meet_vars)):
            if i != j:
                name_i, loc_i, _, _, _, start_i, end_i = meet_vars[i]
                name_j, loc_j, _, _, _, start_j, _ = meet_vars[j]
                # If meeting j is after meeting i, add travel time
                s.add(Implies(start_j > end_i, start_j >= end_i + travel_times[locations[loc_i]][locations[loc_j]]))

    # Initial travel from Marina District to first meeting
    for i in range(len(meet_vars)):
        name, loc, _, _, _, start, _ = meet_vars[i]
        s.add(start >= current_time + travel_times[current_location][locations[loc]])

    # Ensure no overlapping meetings
    for i in range(len(meet_vars)):
        for j in range(i + 1, len(meet_vars)):
            _, _, _, _, _, start_i, end_i = meet_vars[i]
            _, _, _, _, _, start_j, end_j = meet_vars[j]
            s.add(Or(end_i <= start_j, end_j <= start_i))

    # Objective: maximize the number of friends met
    # We'll use a soft constraint approach (try to meet all, then relax if unsat)
    # For simplicity, we'll first try to meet all friends, then adjust if needed

    if s.check() == sat:
        m = s.model()
        schedule = []
        for name, loc, _, _, _, start, end in meet_vars:
            start_val = m.evaluate(start).as_long()
            end_val = m.evaluate(end).as_long()
            schedule.append((name, loc, start_val, end_val))
        schedule.sort(key=lambda x: x[2])  # Sort by start time
        return schedule
    else:
        return None

schedule = solve_scheduling()
if schedule:
    print("SOLUTION:")
    print("Optimal Schedule:")
    for name, loc, start, end in schedule:
        start_hr = start // 60
        start_min = start % 60
        end_hr = end // 60
        end_min = end % 60
        print(f"Meet {name} at {loc} from {start_hr:02d}:{start_min:02d} to {end_hr:02d}:{end_min:02d}")
else:
    print("No feasible schedule found.")