from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Define locations
    locations = ["Golden Gate Park", "Haight-Ashbury", "Fisherman's Wharf", 
                "The Castro", "Chinatown", "Alamo Square", "North Beach", "Russian Hill"]
    loc_index = {loc:i for i, loc in enumerate(locations)}

    # Travel times matrix (minutes)
    travel_time = [
        [0, 7, 24, 13, 23, 10, 24, 19],
        [7, 0, 23, 6, 19, 5, 19, 17],
        [25, 22, 0, 26, 12, 20, 6, 7],
        [11, 6, 24, 0, 20, 8, 20, 18],
        [23, 19, 8, 22, 0, 17, 3, 7],
        [9, 5, 19, 8, 16, 0, 15, 13],
        [22, 18, 5, 22, 6, 16, 0, 4],
        [21, 17, 7, 21, 9, 15, 5, 0]
    ]

    # Friends data: (name, location, start_time, end_time, min_duration)
    friends = [
        ("Carol", "Haight-Ashbury", 21*60+30, 22*60+30, 60),
        ("Laura", "Fisherman's Wharf", 11*60+45, 21*60+30, 60),
        ("Karen", "The Castro", 7*60+15, 14*60, 75),
        ("Elizabeth", "Chinatown", 12*60+15, 21*60+30, 75),
        ("Deborah", "Alamo Square", 12*60, 15*60, 105),
        ("Jason", "North Beach", 14*60+45, 19*60, 90),
        ("Steven", "Russian Hill", 14*60+45, 18*60+30, 120)
    ]

    # Decision variables
    meet = [Bool(f"meet_{i}") for i in range(len(friends))]
    start = [Int(f"start_{i}") for i in range(len(friends))]
    end = [Int(f"end_{i}") for i in range(len(friends))]
    visit_order = [Int(f"visit_{i}") for i in range(len(friends))]

    # Initial conditions
    current_time = Int("initial_time")
    s.add(current_time == 9*60)  # Start at 9:00 AM
    current_loc = Int("initial_loc")
    s.add(current_loc == loc_index["Golden Gate Park"])

    # Constraints for each friend
    for i in range(len(friends)):
        name, loc, f_start, f_end, duration = friends[i]
        loc_idx = loc_index[loc]

        # If meeting this friend
        s.add(Implies(meet[i], start[i] >= f_start))
        s.add(Implies(meet[i], end[i] <= f_end))
        s.add(Implies(meet[i], end[i] - start[i] >= duration))
        s.add(Implies(meet[i], visit_order[i] >= 0))

        # If not meeting this friend
        s.add(Implies(Not(meet[i]), visit_order[i] == -1))
        s.add(Implies(Not(meet[i]), start[i] == 0))
        s.add(Implies(Not(meet[i]), end[i] == 0))

    # Visit ordering constraints
    for i in range(len(friends)):
        for j in range(i+1, len(friends)):
            # If both are being met, their visit orders must be distinct
            s.add(Implies(And(meet[i], meet[j]), visit_order[i] != visit_order[j]))

    # Travel time constraints
    for i in range(len(friends)):
        for j in range(len(friends)):
            if i != j:
                # If meeting j after i
                s.add(Implies(
                    And(meet[i], meet[j], visit_order[i] < visit_order[j]),
                    start[j] >= end[i] + travel_time[loc_index[friends[i][1]]][loc_index[friends[j][1]]]
                ))

    # Objective: maximize number of friends met
    s.maximize(Sum([If(meet[i], 1, 0) for i in range(len(friends))])

    # Solve
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        print(f"Total friends met: {sum(1 for i in range(len(friends)) if is_true(m.evaluate(meet[i]))}")
        
        # Get visit order
        visits = []
        for i in range(len(friends)):
            if is_true(m.evaluate(meet[i])):
                visits.append((
                    m.evaluate(visit_order[i]).as_long(),
                    friends[i][0],
                    friends[i][1],
                    m.evaluate(start[i]).as_long(),
                    m.evaluate(end[i]).as_long()
                ))
        
        # Sort by visit order
        visits.sort()
        
        # Print schedule
        current_time = 9*60
        current_loc = "Golden Gate Park"
        for visit in visits:
            _, name, loc, start_t, end_t = visit
            travel = travel_time[loc_index[current_loc]][loc_index[loc]]
            print(f"Travel from {current_loc} to {loc} ({travel} mins)")
            print(f"Meet {name} at {loc} from {start_t//60}:{start_t%60:02d} to {end_t//60}:{end_t%60:02d}")
            current_time = end_t
            current_loc = loc
    else:
        print("No valid schedule found")

solve_scheduling()