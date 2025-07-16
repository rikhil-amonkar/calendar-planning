from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Locations and their indices
    locations = ["The Castro", "Bayview", "Pacific Heights", "Alamo Square", 
                 "Fisherman's Wharf", "Golden Gate Park"]
    loc_index = {loc: i for i, loc in enumerate(locations)}

    # Travel times matrix (minutes)
    travel = [
        [0, 19, 16, 8, 24, 11],    # The Castro
        [20, 0, 23, 16, 25, 22],   # Bayview
        [16, 22, 0, 10, 13, 15],    # Pacific Heights
        [8, 16, 10, 0, 19, 9],     # Alamo Square
        [26, 26, 12, 20, 0, 25],    # Fisherman's Wharf
        [13, 23, 16, 10, 24, 0]     # Golden Gate Park
    ]

    # Friend data: name, location, available start, available end, min duration
    friends = [
        ("Rebecca", "Bayview", 540, 765, 90),      # 9:00-12:45
        ("Amanda", "Pacific Heights", 1110, 1305, 90),  # 18:30-21:45
        ("James", "Alamo Square", 585, 1275, 90),  # 9:45-21:15
        ("Sarah", "Fisherman's Wharf", 480, 1290, 90), # 8:00-21:30
        ("Melissa", "Golden Gate Park", 540, 1125, 90) # 9:00-18:45
    ]

    # Decision variables
    meet = [Bool(f"meet_{name}") for name, _, _, _, _ in friends]
    start = [Int(f"start_{name}") for name, _, _, _, _ in friends]
    end = [Int(f"end_{name}") for name, _, _, _, _ in friends]
    order = [Int(f"order_{name}") for name, _, _, _, _ in friends]

    # All order variables must be distinct and between 1 and number of friends
    s.add(Distinct(order))
    for o in order:
        s.add(o >= 1, o <= len(friends))

    # Initial conditions
    current_time = 540  # Start at 9:00 at The Castro
    current_loc = loc_index["The Castro"]

    # For each possible meeting position in sequence
    for pos in range(1, len(friends)+1):
        for i, (name, loc, f_start, f_end, min_dur) in enumerate(friends):
            loc_idx = loc_index[loc]
            
            # If this friend is at position 'pos' in the schedule
            at_pos = (order[i] == pos)
            
            # Constraints when meeting this friend at this position
            s.add(Implies(And(meet[i], at_pos),
                And(
                    start[i] >= f_start,
                    end[i] <= f_end,
                    end[i] - start[i] >= min_dur,
                    start[i] >= current_time + travel[current_loc][loc_idx]
                )))
            
            # Update current time and location if we meet here
            current_time = If(And(meet[i], at_pos), end[i], current_time)
            current_loc = If(And(meet[i], at_pos), loc_idx, current_loc)

    # If not meeting a friend, set their times to 0
    for i in range(len(friends)):
        s.add(Implies(Not(meet[i]), And(start[i] == 0, end[i] == 0)))

    # Objective: maximize number of friends met
    s.maximize(Sum([If(m, 1, 0) for m in meet]))

    # Solve
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        # Get meeting order
        schedule = sorted([(m.evaluate(order[i]).as_long(), i) 
                          for i in range(len(friends)) if m.evaluate(meet[i])])
        
        current_time = 540
        current_loc = loc_index["The Castro"]
        
        for pos, i in schedule:
            name, loc, _, _, _ = friends[i]
            start_time = m.evaluate(start[i]).as_long()
            end_time = m.evaluate(end[i]).as_long()
            travel_time = travel[current_loc][loc_index[loc]]
            
            print(f"Travel from {locations[current_loc]} to {loc} ({travel_time} mins)")
            print(f"Meet {name} at {loc} from {start_time//60}:{start_time%60:02d} to {end_time//60}:{end_time%60:02d}")
            
            current_time = end_time
            current_loc = loc_index[loc]
        
        # Print friends not met
        for i in range(len(friends)):
            if not m.evaluate(meet[i]):
                print(f"Cannot meet {friends[i][0]}")
    else:
        print("No valid schedule found")

solve_scheduling()