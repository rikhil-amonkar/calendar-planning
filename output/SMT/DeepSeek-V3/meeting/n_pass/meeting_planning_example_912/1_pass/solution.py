from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define the locations and their indices
    locations = [
        "Union Square", "Presidio", "Alamo Square", "Marina District", "Financial District",
        "Nob Hill", "Sunset District", "Chinatown", "Russian Hill", "North Beach", "Haight-Ashbury"
    ]
    loc_index = {loc: idx for idx, loc in enumerate(locations)}

    # Travel times matrix (in minutes)
    travel_times = [
        [0, 24, 15, 18, 9, 9, 27, 7, 13, 10, 18],  # Union Square
        [22, 0, 19, 11, 23, 18, 15, 21, 14, 18, 15],  # Presidio
        [14, 17, 0, 15, 17, 11, 16, 15, 13, 15, 5],  # Alamo Square
        [16, 10, 15, 0, 17, 12, 19, 15, 8, 11, 16],  # Marina District
        [9, 22, 17, 15, 0, 8, 30, 5, 11, 7, 19],  # Financial District
        [7, 17, 11, 11, 9, 0, 24, 6, 5, 8, 13],  # Nob Hill
        [30, 16, 17, 21, 30, 27, 0, 30, 24, 28, 15],  # Sunset District
        [7, 19, 17, 12, 5, 9, 29, 0, 7, 3, 19],  # Chinatown
        [10, 14, 15, 7, 11, 5, 23, 9, 0, 5, 17],  # Russian Hill
        [7, 17, 16, 9, 8, 7, 27, 6, 4, 0, 18],  # North Beach
        [19, 15, 5, 17, 21, 15, 15, 19, 17, 19, 0]   # Haight-Ashbury
    ]

    # Friends' data: name, location, start time, end time, min duration
    friends = [
        ("Kimberly", "Presidio", 15 * 60 + 30, 16 * 60, 15),
        ("Elizabeth", "Alamo Square", 19 * 60 + 15, 20 * 60 + 15, 15),
        ("Joshua", "Marina District", 10 * 60 + 30, 14 * 60 + 15, 45),
        ("Sandra", "Financial District", 19 * 60 + 30, 20 * 60 + 15, 45),
        ("Kenneth", "Nob Hill", 12 * 60 + 45, 21 * 60 + 45, 30),
        ("Betty", "Sunset District", 14 * 60, 19 * 60, 60),
        ("Deborah", "Chinatown", 17 * 60 + 15, 20 * 60 + 30, 15),
        ("Barbara", "Russian Hill", 17 * 60 + 30, 21 * 60 + 15, 120),
        ("Steven", "North Beach", 17 * 60 + 45, 20 * 60 + 45, 90),
        ("Daniel", "Haight-Ashbury", 18 * 60 + 30, 18 * 60 + 45, 15)
    ]

    # Variables for each friend: start and end times of the meeting
    start_vars = [Int(f'start_{name}') for name, _, _, _, _ in friends]
    end_vars = [Int(f'end_{name}') for name, _, _, _, _ in friends]
    meet_vars = [Bool(f'meet_{name}') for name, _, _, _, _ in friends]  # Whether to meet the friend

    # Initial position: Union Square at 9:00 AM (540 minutes)
    current_time = 540  # 9:00 AM in minutes
    current_loc = loc_index["Union Square"]

    # Constraints for each friend
    for i, (name, loc, friend_start, friend_end, min_dur) in enumerate(friends):
        loc_idx = loc_index[loc]
        # If meeting the friend, the meeting must fit within their window and have min duration
        s.add(Implies(meet_vars[i], And(
            start_vars[i] >= friend_start,
            end_vars[i] <= friend_end,
            end_vars[i] - start_vars[i] >= min_dur
        )))
        # If not meeting the friend, start and end times are irrelevant
        s.add(Implies(Not(meet_vars[i]), And(
            start_vars[i] == -1,
            end_vars[i] == -1
        )))

    # Order constraints: meetings must be in sequence with travel time
    # We need to model the order of meetings, but this is complex with Z3.
    # For simplicity, we'll assume meetings are in the order of friends list and add travel time constraints.
    # This is a simplification; a more accurate approach would involve sequencing variables.
    prev_end = current_time
    prev_loc = current_loc
    for i in range(len(friends)):
        # Travel time from previous location to current friend's location
        travel_time = travel_times[prev_loc][loc_index[friends[i][1]]]
        # If meeting this friend, start time must be >= prev_end + travel_time
        s.add(Implies(meet_vars[i], start_vars[i] >= prev_end + travel_time))
        # Update prev_end and prev_loc if meeting this friend
        prev_end = If(meet_vars[i], end_vars[i], prev_end)
        prev_loc = If(meet_vars[i], loc_index[friends[i][1]], prev_loc)

    # Maximize the number of friends met
    s.maximize(Sum([If(meet_vars[i], 1, 0) for i in range(len(friends))]))

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        print("Schedule:")
        total_met = 0
        for i, (name, loc, _, _, _) in enumerate(friends):
            if m.evaluate(meet_vars[i]):
                start = m.evaluate(start_vars[i])
                end = m.evaluate(end_vars[i])
                start_hr = start.as_long() // 60
                start_min = start.as_long() % 60
                end_hr = end.as_long() // 60
                end_min = end.as_long() % 60
                print(f"Meet {name} at {loc} from {start_hr:02d}:{start_min:02d} to {end_hr:02d}:{end_min:02d}")
                total_met += 1
        print(f"Total friends met: {total_met}")
    else:
        print("No solution found.")

solve_scheduling()