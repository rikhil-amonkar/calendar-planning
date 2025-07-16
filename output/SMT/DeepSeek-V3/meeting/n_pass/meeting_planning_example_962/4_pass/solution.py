from z3 import *

def solve_scheduling():
    # Initialize solver
    solver = Optimize()

    # Define locations and indices
    locations = [
        "The Castro", "Marina District", "Presidio", "North Beach", "Embarcadero",
        "Haight-Ashbury", "Golden Gate Park", "Richmond District", "Alamo Square",
        "Financial District", "Sunset District"
    ]
    loc_index = {loc: idx for idx, loc in enumerate(locations)}

    # Travel times matrix (minutes)
    travel_time = [
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

    # Friends data: name, location, available start, available end, min duration
    friends = [
        ("Elizabeth", "Marina District", 19*60, 20*60+45, 105),
        ("Joshua", "Presidio", 8*60+30, 13*60+15, 105),
        ("Timothy", "North Beach", 19*60+45, 22*60, 90),
        ("David", "Embarcadero", 10*60+45, 12*60+30, 30),
        ("Kimberly", "Haight-Ashbury", 16*60+45, 21*60+30, 75),
        ("Lisa", "Golden Gate Park", 17*60+30, 21*60+45, 45),
        ("Ronald", "Richmond District", 8*60, 9*60+30, 90),
        ("Stephanie", "Alamo Square", 15*60+30, 16*60+30, 30),
        ("Helen", "Financial District", 17*60+30, 18*60+30, 45),
        ("Laura", "Sunset District", 17*60+45, 21*60+15, 90)
    ]

    # Create variables
    meets = [Bool(f"meet_{name}") for name, _, _, _, _ in friends]
    starts = [Int(f"start_{name}") for name, _, _, _, _ in friends]
    ends = [Int(f"end_{name}") for name, _, _, _, _ in friends]

    # Current time starts at 9:00 AM (540 minutes)
    current_time = Int("current_time")
    solver.add(current_time == 540)
    current_loc = loc_index["The Castro"]

    # Meeting constraints
    for i, (name, loc, a_start, a_end, dur) in enumerate(friends):
        loc_idx = loc_index[loc]
        
        # If meeting this friend
        solver.add(Implies(meets[i], starts[i] >= a_start))
        solver.add(Implies(meets[i], ends[i] <= a_end))
        solver.add(Implies(meets[i], ends[i] - starts[i] >= dur))
        
        # Travel time constraint
        solver.add(Implies(meets[i], starts[i] >= current_time + travel_time[current_loc][loc_idx]))
        
        # Update current time and location
        new_time = If(meets[i], ends[i], current_time)
        new_loc = If(meets[i], loc_idx, current_loc)
        current_time = new_time
        current_loc = new_loc

    # Maximize number of friends met
    solver.maximize(Sum([If(m, 1, 0) for m in meets]))

    # Solve and print results
    if solver.check() == sat:
        m = solver.model()
        print("SOLUTION:")
        print("Friends you can meet:")
        schedule = []
        for i, (name, loc, _, _, _) in enumerate(friends):
            if m.eval(meets[i]):
                start = m.eval(starts[i]).as_long()
                end = m.eval(ends[i]).as_long()
                start_str = f"{start//60:02d}:{start%60:02d}"
                end_str = f"{end//60:02d}:{end%60:02d}"
                print(f"- {name} at {loc} from {start_str} to {end_str}")
                schedule.append((name, loc, start_str, end_str))
        
        print("\nOptimal Schedule:")
        for i, (name, loc, start, end) in enumerate(schedule, 1):
            print(f"{i}. Meet {name} at {loc} ({start} - {end})")
    else:
        print("No valid schedule found that meets all constraints")

if __name__ == "__main__":
    solve_scheduling()