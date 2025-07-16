from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Locations
    locations = ["The Castro", "Bayview", "Pacific Heights", "Alamo Square", 
                "Fisherman's Wharf", "Golden Gate Park"]
    loc_idx = {loc: i for i, loc in enumerate(locations)}

    # Travel times matrix (minutes)
    travel = [
        [0, 19, 16, 8, 24, 11],    # The Castro
        [20, 0, 23, 16, 25, 22],   # Bayview
        [16, 22, 0, 10, 13, 15],   # Pacific Heights
        [8, 16, 10, 0, 19, 9],     # Alamo Square
        [26, 26, 12, 20, 0, 25],   # Fisherman's Wharf
        [13, 23, 16, 10, 24, 0]    # Golden Gate Park
    ]

    # Friend data: (name, location, available start, available end, min duration)
    friends = [
        ("Rebecca", "Bayview", 540, 765, 90),      # 9:00-12:45
        ("Amanda", "Pacific Heights", 1110, 1305, 90),  # 18:30-21:45
        ("James", "Alamo Square", 585, 1275, 90),   # 9:45-21:15
        ("Sarah", "Fisherman's Wharf", 480, 1290, 90),  # 8:00-21:30
        ("Melissa", "Golden Gate Park", 540, 1125, 90)  # 9:00-18:45
    ]

    # Decision variables
    meet = [Bool(f"meet_{name}") for name, _, _, _, _ in friends]
    start = [Int(f"start_{name}") for name, _, _, _, _ in friends]
    end = [Int(f"end_{name}") for name, _, _, _, _ in friends]
    visit_order = [Int(f"order_{name}") for name, _, _, _, _ in friends]

    # Each friend has a unique visit order (if met)
    s.add(Distinct([If(meet[i], visit_order[i], 0) for i in range(len(friends))])
    for i in range(len(friends)):
        s.add(Implies(meet[i], visit_order[i] >= 1))
        s.add(Implies(Not(meet[i]), visit_order[i] == 0))

    # Initial conditions
    current_time = Int("current_time")
    s.add(current_time == 540)  # Start at 9:00 AM
    current_loc = Int("current_loc")
    s.add(current_loc == loc_idx["The Castro"])

    # For each friend, if met, set constraints
    for i, (name, loc, f_start, f_end, min_dur) in enumerate(friends):
        loc_i = loc_idx[loc]
        
        # Meeting time constraints
        s.add(Implies(meet[i],
            And(
                start[i] >= f_start,
                end[i] <= f_end,
                end[i] - start[i] >= min_dur,
                start[i] >= current_time + travel[current_loc][loc_i]
            )))
        
        # Update current time and location if we meet this friend
        current_time = If(meet[i], end[i], current_time)
        current_loc = If(meet[i], loc_i, current_loc)

        # If not meeting, set times to 0
        s.add(Implies(Not(meet[i]), And(start[i] == 0, end[i] == 0)))

    # Objective: maximize number of friends met
    s.maximize(Sum([If(m, 1, 0) for m in meet]))

    # Solve
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        
        # Collect meetings
        meetings = []
        for i, (name, loc, _, _, _) in enumerate(friends):
            if m.evaluate(meet[i]):
                order = m.evaluate(visit_order[i]).as_long()
                st = m.evaluate(start[i]).as_long()
                en = m.evaluate(end[i]).as_long()
                meetings.append((order, name, loc, st, en))
        
        # Sort by visit order
        meetings.sort()
        
        # Print schedule
        prev_loc = "The Castro"
        prev_time = 540
        for order, name, loc, st, en in meetings:
            travel_time = travel[loc_idx[prev_loc]][loc_idx[loc]]
            print(f"Travel from {prev_loc} to {loc} ({travel_time} mins)")
            print(f"Meet {name} at {loc} from {st//60}:{st%60:02d} to {en//60}:{en%60:02d}")
            prev_loc = loc
            prev_time = en
        
        # Print missed friends
        for i, (name, _, _, _, _) in enumerate(friends):
            if not m.evaluate(meet[i]):
                print(f"Cannot meet {name}")
    else:
        print("No valid schedule found")

solve_scheduling()