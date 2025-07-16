from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Locations and travel times (in minutes)
    locations = ["The Castro", "Bayview", "Pacific Heights", "Alamo Square", 
                "Fisherman's Wharf", "Golden Gate Park"]
    travel_times = {
        ("The Castro", "Bayview"): 19,
        ("The Castro", "Pacific Heights"): 16,
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "Fisherman's Wharf"): 24,
        ("The Castro", "Golden Gate Park"): 11,
        ("Bayview", "The Castro"): 20,
        ("Bayview", "Pacific Heights"): 23,
        ("Bayview", "Alamo Square"): 16,
        ("Bayview", "Fisherman's Wharf"): 25,
        ("Bayview", "Golden Gate Park"): 22,
        ("Pacific Heights", "The Castro"): 16,
        ("Pacific Heights", "Bayview"): 22,
        ("Pacific Heights", "Alamo Square"): 10,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
        ("Pacific Heights", "Golden Gate Park"): 15,
        ("Alamo Square", "The Castro"): 8,
        ("Alamo Square", "Bayview"): 16,
        ("Alamo Square", "Pacific Heights"): 10,
        ("Alamo Square", "Fisherman's Wharf"): 19,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Fisherman's Wharf", "The Castro"): 26,
        ("Fisherman's Wharf", "Bayview"): 26,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Fisherman's Wharf", "Alamo Square"): 20,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Golden Gate Park", "The Castro"): 13,
        ("Golden Gate Park", "Bayview"): 23,
        ("Golden Gate Park", "Pacific Heights"): 16,
        ("Golden Gate Park", "Alamo Square"): 10,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
    }

    # Friend data: (name, location, available start, available end, min duration in minutes)
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

    # Constraints for order variables
    s.add(Distinct(order))
    for o in order:
        s.add(o >= 1, o <= len(friends))

    # Initial conditions
    current_time = Int("initial_time")
    s.add(current_time == 540)  # Start at 9:00 AM
    current_loc = "The Castro"

    # For each possible position in the schedule
    for pos in range(1, len(friends)+1):
        for i, (name, loc, f_start, f_end, min_dur) in enumerate(friends):
            # If this friend is at this position
            at_pos = (order[i] == pos)
            
            # Travel time from current location
            travel_time = travel_times.get((current_loc, loc), 0)
            
            # Constraints when meeting this friend at this position
            s.add(Implies(And(meet[i], at_pos),
                And(
                    start[i] >= f_start,
                    end[i] <= f_end,
                    end[i] - start[i] >= min_dur,
                    start[i] >= current_time + travel_time
                ))
            
            # Update current time and location if we meet here
            current_time = If(And(meet[i], at_pos), end[i], current_time)
            current_loc = If(And(meet[i], at_pos), loc, current_loc)

    # If not meeting a friend, set their times to 0
    for i in range(len(friends)):
        s.add(Implies(Not(meet[i]), And(start[i] == 0, end[i] == 0)))

    # Objective: maximize number of friends met
    s.maximize(Sum([If(m, 1, 0) for m in meet]))

    # Solve
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        
        # Get schedule in order
        schedule = []
        for i in range(len(friends)):
            if m.evaluate(meet[i]):
                pos = m.evaluate(order[i]).as_long()
                name = friends[i][0]
                loc = friends[i][1]
                start_time = m.evaluate(start[i]).as_long()
                end_time = m.evaluate(end[i]).as_long()
                schedule.append((pos, name, loc, start_time, end_time))
        
        # Sort by position and print
        schedule.sort()
        current_loc = "The Castro"
        current_time = 540
        
        for pos, name, loc, start_time, end_time in schedule:
            travel_time = travel_times.get((current_loc, loc), 0)
            print(f"Travel from {current_loc} to {loc} ({travel_time} mins)")
            print(f"Meet {name} at {loc} from {start_time//60}:{start_time%60:02d} to {end_time//60}:{end_time%60:02d}")
            current_loc = loc
            current_time = end_time
        
        # Print friends not met
        for i in range(len(friends)):
            if not m.evaluate(meet[i]):
                print(f"Cannot meet {friends[i][0]}")
    else:
        print("No valid schedule found")

solve_scheduling()