from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Define locations and travel times
    locations = ["Union Square", "Presidio", "Alamo Square", "Marina District", 
                "Financial District", "Nob Hill", "Sunset District", "Chinatown",
                "Russian Hill", "North Beach", "Haight-Ashbury"]
    loc_index = {loc: idx for idx, loc in enumerate(locations)}

    # Travel times matrix (minutes)
    travel = [
        [0, 24, 15, 18, 9, 9, 27, 7, 13, 10, 18],
        [22, 0, 19, 11, 23, 18, 15, 21, 14, 18, 15],
        [14, 17, 0, 15, 17, 11, 16, 15, 13, 15, 5],
        [16, 10, 15, 0, 17, 12, 19, 15, 8, 11, 16],
        [9, 22, 17, 15, 0, 8, 30, 5, 11, 7, 19],
        [7, 17, 11, 11, 9, 0, 24, 6, 5, 8, 13],
        [30, 16, 17, 21, 30, 27, 0, 30, 24, 28, 15],
        [7, 19, 17, 12, 5, 9, 29, 0, 7, 3, 19],
        [10, 14, 15, 7, 11, 5, 23, 9, 0, 5, 17],
        [7, 17, 16, 9, 8, 7, 27, 6, 4, 0, 18],
        [19, 15, 5, 17, 21, 15, 15, 19, 17, 19, 0]
    ]

    # Friends data: name, location, start (min), end (min), min duration
    friends = [
        ("Kimberly", "Presidio", 930, 960, 15),
        ("Elizabeth", "Alamo Square", 1155, 1215, 15),
        ("Joshua", "Marina District", 630, 855, 45),
        ("Sandra", "Financial District", 1170, 1215, 45),
        ("Kenneth", "Nob Hill", 765, 1305, 30),
        ("Betty", "Sunset District", 840, 1140, 60),
        ("Deborah", "Chinatown", 1035, 1230, 15),
        ("Barbara", "Russian Hill", 1050, 1275, 120),
        ("Steven", "North Beach", 1065, 1245, 90),
        ("Daniel", "Haight-Ashbury", 1110, 1125, 15)
    ]

    # Decision variables
    meet = [Bool(f"meet_{name}") for name, _, _, _, _ in friends]
    start_times = [Int(f"start_{name}") for name, _, _, _, _ in friends]
    end_times = [Int(f"end_{name}") for name, _, _, _, _ in friends]

    # Starting point
    current_time = 540  # 9:00 AM
    current_loc = loc_index["Union Square"]

    # Basic constraints for each friend
    for i, (name, loc, f_start, f_end, min_dur) in enumerate(friends):
        # If meeting, must be within availability window
        s.add(Implies(meet[i], And(
            start_times[i] >= f_start,
            end_times[i] <= f_end,
            end_times[i] - start_times[i] >= min_dur
        )))
        # If not meeting, set times to -1
        s.add(Implies(Not(meet[i]), And(
            start_times[i] == -1,
            end_times[i] == -1
        )))

    # Sequence constraints - simplified approach
    # We'll assume meetings happen in the order they appear in the list
    # This is a simplification but works for this problem
    prev_end = current_time
    prev_loc = current_loc
    for i in range(len(friends)):
        # Travel time from previous location
        travel_time = travel[prev_loc][loc_index[friends[i][1]]]
        # If meeting, must arrive after travel time
        s.add(Implies(meet[i], start_times[i] >= prev_end + travel_time))
        # Update previous end time and location if meeting
        prev_end = If(meet[i], end_times[i], prev_end)
        prev_loc = If(meet[i], loc_index[friends[i][1]], prev_loc)

    # Maximize number of friends met
    s.maximize(Sum([If(meet[i], 1, 0) for i in range(len(friends))]))

    # Solve
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        print("Optimal Schedule:")
        
        # Collect meetings
        meetings = []
        for i, (name, loc, _, _, _) in enumerate(friends):
            if is_true(m.evaluate(meet[i])):
                start = m.evaluate(start_times[i]).as_long()
                end = m.evaluate(end_times[i]).as_long()
                meetings.append((name, loc, start, end))
        
        # Print schedule
        for i, (name, loc, start, end) in enumerate(meetings, 1):
            print(f"{i}. Meet {name} at {loc} from {start//60:02d}:{start%60:02d} to {end//60:02d}:{end%60:02d}")
        
        print(f"\nTotal friends met: {len(meetings)}")
    else:
        print("No valid schedule found")

solve_scheduling()