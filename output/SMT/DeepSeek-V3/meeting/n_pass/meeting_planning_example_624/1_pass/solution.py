from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define the locations and their indices
    locations = {
        "Golden Gate Park": 0,
        "Haight-Ashbury": 1,
        "Fisherman's Wharf": 2,
        "The Castro": 3,
        "Chinatown": 4,
        "Alamo Square": 5,
        "North Beach": 6,
        "Russian Hill": 7
    }

    # Travel times matrix (in minutes)
    travel_times = [
        [0, 7, 24, 13, 23, 10, 24, 19],  # Golden Gate Park
        [7, 0, 23, 6, 19, 5, 19, 17],     # Haight-Ashbury
        [25, 22, 0, 26, 12, 20, 6, 7],    # Fisherman's Wharf
        [11, 6, 24, 0, 20, 8, 20, 18],     # The Castro
        [23, 19, 8, 22, 0, 17, 3, 7],      # Chinatown
        [9, 5, 19, 8, 16, 0, 15, 13],      # Alamo Square
        [22, 18, 5, 22, 6, 16, 0, 4],      # North Beach
        [21, 17, 7, 21, 9, 15, 5, 0]       # Russian Hill
    ]

    # Friends' data: name, location, start time, end time, min duration (in minutes)
    friends = [
        ("Carol", "Haight-Ashbury", 21 * 60 + 30, 22 * 60 + 30, 60),
        ("Laura", "Fisherman's Wharf", 11 * 60 + 45, 21 * 60 + 30, 60),
        ("Karen", "The Castro", 7 * 60 + 15, 14 * 60, 75),
        ("Elizabeth", "Chinatown", 12 * 60 + 15, 21 * 60 + 30, 75),
        ("Deborah", "Alamo Square", 12 * 60, 15 * 60, 105),
        ("Jason", "North Beach", 14 * 60 + 45, 19 * 60, 90),
        ("Steven", "Russian Hill", 14 * 60 + 45, 18 * 60 + 30, 120)
    ]

    # Convert all times to minutes since 9:00 AM (540 minutes)
    start_time = 9 * 60  # 9:00 AM in minutes

    # Variables for each friend: start and end of meeting
    meet_start = [Int(f'meet_start_{i}') for i in range(len(friends))]
    meet_end = [Int(f'meet_end_{i}') for i in range(len(friends))]
    meet_loc = [locations[friend[1]] for friend in friends]

    # Variables to track whether a friend is met
    met = [Bool(f'met_{i}') for i in range(len(friends))]

    # Initial position is Golden Gate Park (index 0)
    current_loc = 0
    current_time = start_time

    # Constraints for each friend
    for i in range(len(friends)):
        name, loc, friend_start, friend_end, min_duration = friends[i]
        loc_idx = locations[loc]

        # If the friend is met, their meeting must fit within their availability and duration
        s.add(Implies(met[i], meet_start[i] >= friend_start))
        s.add(Implies(met[i], meet_end[i] <= friend_end))
        s.add(Implies(met[i], meet_end[i] - meet_start[i] >= min_duration))

        # Travel time from current location to friend's location
        travel_time = travel_times[current_loc][loc_idx]
        s.add(Implies(met[i], meet_start[i] >= current_time + travel_time))

        # Update current location and time if the friend is met
        new_current_loc = loc_idx
        new_current_time = meet_end[i]
        s.add(Implies(met[i], current_loc == new_current_loc))
        s.add(Implies(met[i], current_time == new_current_time))

    # Maximize the number of friends met
    total_met = Sum([If(met[i], 1, 0) for i in range(len(friends))])
    s.maximize(total_met)

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        print(f"Total friends met: {m.evaluate(total_met)}")
        for i in range(len(friends)):
            if m.evaluate(met[i]):
                start = m.evaluate(meet_start[i])
                end = m.evaluate(meet_end[i])
                print(f"Meet {friends[i][0]} at {friends[i][1]} from {start // 60}:{start % 60:02d} to {end // 60}:{end % 60:02d}")
    else:
        print("No solution found")

solve_scheduling()