from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define the locations and their indices
    locations = [
        "The Castro", "Marina District", "Presidio", "North Beach", "Embarcadero",
        "Haight-Ashbury", "Golden Gate Park", "Richmond District", "Alamo Square",
        "Financial District", "Sunset District"
    ]
    loc_index = {loc: idx for idx, loc in enumerate(locations)}

    # Travel times matrix (in minutes)
    travel_times = [
        [0, 21, 20, 20, 22, 6, 11, 16, 8, 21, 17],
        [22, 0, 10, 11, 14, 16, 18, 11, 15, 17, 19],
        [21, 11, 0, 18, 20, 15, 12, 7, 19, 23, 15],
        [23, 9, 17, 0, 6, 18, 22, 18, 16, 8, 27],
        [25, 12, 20, 5, 0, 21, 25, 21, 19, 5, 30],
        [6, 17, 15, 19, 20, 0, 7, 10, 5, 21, 15],
        [13, 16, 11, 23, 25, 7, 0, 7, 9, 26, 10],
        [16, 9, 7, 17, 19, 10, 9, 0, 13, 22, 11],
        [8, 15, 17, 15, 16, 5, 9, 11, 0, 17, 16],
        [20, 15, 22, 7, 4, 19, 23, 21, 17, 0, 30],
        [17, 21, 16, 28, 30, 15, 11, 12, 17, 30, 0]
    ]

    # Friends' data: name, location, available start (minutes), available end (minutes), min duration (minutes)
    friends = [
        ("Elizabeth", "Marina District", 19*60, 20*60 + 45, 105),
        ("Joshua", "Presidio", 8*60 + 30, 13*60 + 15, 105),
        ("Timothy", "North Beach", 19*60 + 45, 22*60, 90),
        ("David", "Embarcadero", 10*60 + 45, 12*60 + 30, 30),
        ("Kimberly", "Haight-Ashbury", 16*60 + 45, 21*60 + 30, 75),
        ("Lisa", "Golden Gate Park", 17*60 + 30, 21*60 + 45, 45),
        ("Ronald", "Richmond District", 8*60, 9*60 + 30, 90),
        ("Stephanie", "Alamo Square", 15*60 + 30, 16*60 + 30, 30),
        ("Helen", "Financial District", 17*60 + 30, 18*60 + 30, 45),
        ("Laura", "Sunset District", 17*60 + 45, 21*60 + 15, 90)
    ]

    # Create variables for each friend: start and end times
    starts = [Int(f'start_{name}') for name, _, _, _, _ in friends]
    ends = [Int(f'end_{name}') for name, _, _, _, _ in friends]
    meets = [Bool(f'meet_{name}') for name, _, _, _, _ in friends]  # Whether we meet this friend

    # Current location starts at The Castro at 9:00 AM (540 minutes)
    current_time = Int('initial_time')
    s.add(current_time == 540)
    current_loc = loc_index["The Castro"]

    # Constraints for each friend
    for i, (name, loc, avail_start, avail_end, min_dur) in enumerate(friends):
        loc_idx = loc_index[loc]
        travel_time = travel_times[current_loc][loc_idx]

        # If we meet this friend, their start and end times must be within their availability
        s.add(Implies(meets[i], starts[i] >= avail_start))
        s.add(Implies(meets[i], ends[i] <= avail_end))
        s.add(Implies(meets[i], ends[i] - starts[i] >= min_dur))

        # Travel time constraint: must arrive at the friend's location by start time
        s.add(Implies(meets[i], starts[i] >= current_time + travel_time))

        # Update current_time and current_loc if we meet this friend
        new_current_time = If(meets[i], ends[i], current_time)
        new_current_loc = If(meets[i], loc_idx, current_loc)
        current_time = new_current_time
        current_loc = new_current_loc

    # Maximize the number of friends met
    s.maximize(Sum([If(meets[i], 1, 0) for i in range(len(friends))]))

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        met_friends = []
        schedule = []

        for i, (name, loc, _, _, _) in enumerate(friends):
            if is_true(m.eval(meets[i])):
                start = m.eval(starts[i]).as_long()
                end = m.eval(ends[i]).as_long()
                start_str = f"{start // 60}:{start % 60:02d}"
                end_str = f"{end // 60}:{end % 60:02d}"
                met_friends.append(name)
                schedule.append((name, loc, start_str, end_str))

        print("SOLUTION:")
        print("Met friends:", met_friends)
        print("Schedule:")
        for entry in schedule:
            print(entry)
    else:
        print("No solution found")

solve_scheduling()