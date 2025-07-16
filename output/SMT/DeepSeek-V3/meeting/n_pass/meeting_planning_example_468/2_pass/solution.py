from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Optimize()

    # Define locations and their indices
    locations = ["The Castro", "Bayview", "Pacific Heights", "Alamo Square", "Fisherman's Wharf", "Golden Gate Park"]
    loc_index = {loc: i for i, loc in enumerate(locations)}

    # Travel times matrix (in minutes)
    travel_times = [
        [0, 19, 16, 8, 24, 11],    # The Castro to others
        [20, 0, 23, 16, 25, 22],   # Bayview to others
        [16, 22, 0, 10, 13, 15],   # Pacific Heights to others
        [8, 16, 10, 0, 19, 9],     # Alamo Square to others
        [26, 26, 12, 20, 0, 25],   # Fisherman's Wharf to others
        [13, 23, 16, 10, 24, 0]    # Golden Gate Park to others
    ]

    # Friend data: name, location, start time, end time, min duration (minutes)
    friends = [
        ("Rebecca", "Bayview", 9*60, 12*60 + 45, 90),
        ("Amanda", "Pacific Heights", 18*60 + 30, 21*60 + 45, 90),
        ("James", "Alamo Square", 9*60 + 45, 21*60 + 15, 90),
        ("Sarah", "Fisherman's Wharf", 8*60, 21*60 + 30, 90),
        ("Melissa", "Golden Gate Park", 9*60, 18*60 + 45, 90)
    ]

    # Create variables for each friend
    meet_vars = [Bool(f"meet_{name}") for name, _, _, _, _ in friends]
    start_vars = [Int(f"start_{name}") for name, _, _, _, _ in friends]
    end_vars = [Int(f"end_{name}") for name, _, _, _, _ in friends]

    # Current time starts at 9:00 AM (540 minutes) at The Castro
    current_time = 540
    current_loc = loc_index["The Castro"]

    # Constraints for each friend
    for i, (name, loc, f_start, f_end, min_dur) in enumerate(friends):
        loc_idx = loc_index[loc]
        
        # If we meet this friend
        s.add(Implies(meet_vars[i], And(
            start_vars[i] >= f_start,
            end_vars[i] <= f_end,
            end_vars[i] - start_vars[i] >= min_dur,
            start_vars[i] >= current_time + travel_times[current_loc][loc_idx]
        )))

        # If we don't meet this friend
        s.add(Implies(Not(meet_vars[i]), And(
            start_vars[i] == 0,
            end_vars[i] == 0
        )))

        # Update current time and location if we meet this friend
        current_time = If(meet_vars[i], end_vars[i], current_time)
        current_loc = If(meet_vars[i], loc_idx, current_loc)

    # Objective: maximize number of friends met
    s.maximize(Sum([If(var, 1, 0) for var in meet_vars]))

    # Solve the problem
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        for i, (name, loc, _, _, _) in enumerate(friends):
            if m.evaluate(meet_vars[i]):
                start = m.evaluate(start_vars[i]).as_long()
                end = m.evaluate(end_vars[i]).as_long()
                print(f"Meet {name} at {loc} from {start//60}:{start%60:02d} to {end//60}:{end%60:02d}")
            else:
                print(f"Cannot meet {name}")
    else:
        print("No valid schedule found")

solve_scheduling()