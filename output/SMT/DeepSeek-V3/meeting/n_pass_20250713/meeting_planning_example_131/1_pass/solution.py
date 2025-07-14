from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Convert all times to minutes since 9:00 AM (540 minutes since midnight)
    # Jason's availability: 10:00 AM (600) to 4:15 PM (975)
    jason_start_min = 600
    jason_end_max = 975
    jason_min_duration = 90

    # Kenneth's availability: 3:30 PM (990) to 4:45 PM (1005)
    kenneth_start_min = 990
    kenneth_end_max = 1005
    kenneth_min_duration = 45

    # Travel times (in minutes)
    ph_to_presidio = 11
    ph_to_marina = 6
    presidio_to_marina = 10
    marina_to_presidio = 10
    presidio_to_ph = 11
    marina_to_ph = 7

    # Variables for meeting start and end times
    # Meeting with Jason
    jason_start = Int('jason_start')
    jason_end = Int('jason_end')
    # Meeting with Kenneth
    kenneth_start = Int('kenneth_start')
    kenneth_end = Int('kenneth_end')

    # Constraints for Jason's meeting
    s.add(jason_start >= jason_start_min)
    s.add(jason_end <= jason_end_max)
    s.add(jason_end - jason_start >= jason_min_duration)

    # Constraints for Kenneth's meeting
    s.add(kenneth_start >= kenneth_start_min)
    s.add(kenneth_end <= kenneth_end_max)
    s.add(kenneth_end - kenneth_start >= kenneth_min_duration)

    # Initial location is Pacific Heights at 9:00 AM (time = 540)
    # We need to decide the order of meetings: Jason first or Kenneth first?

    # Option 1: Meet Jason first, then Kenneth
    # Travel from Pacific Heights to Presidio: 11 minutes
    # So arrival at Presidio at 540 + 11 = 551
    # Jason's meeting must start >= 600, so wait until 600
    # Then after Jason's meeting, travel to Marina District
    # Travel time from Presidio to Marina: 10 minutes
    # So arrival at Marina at jason_end + 10
    # Kenneth's meeting must start >= 990 and >= arrival time
    s.push()
    s.add(jason_start >= 600)  # earliest possible start after travel
    s.add(jason_start >= 540 + ph_to_presidio)  # arrival at Presidio at 551, but earliest start is 600
    s.add(kenneth_start >= jason_end + presidio_to_marina)
    s.add(kenneth_start >= 990)
    s.add(kenneth_end <= 1005)

    # Check if this option is feasible
    if s.check() == sat:
        model = s.model()
        print("Option 1: Meet Jason first, then Kenneth")
        print(f"Meet Jason from {model[jason_start].as_long()} to {model[jason_end].as_long()}")
        print(f"Meet Kenneth from {model[kenneth_start].as_long()} to {model[kenneth_end].as_long()}")
        total_time = (model[jason_end].as_long() - model[jason_start].as_long()) + (model[kenneth_end].as_long() - model[kenneth_start].as_long())
        print(f"Total time with friends: {total_time} minutes")
    else:
        print("Option 1 is not feasible")
    s.pop()

    # Option 2: Meet Kenneth first, then Jason
    # Travel from Pacific Heights to Marina: 6 minutes
    # Arrival at Marina at 540 + 6 = 546
    # Kenneth's availability starts at 990, so wait until 990
    # After Kenneth's meeting, travel to Presidio: 10 minutes
    # Arrival at Presidio at kenneth_end + 10
    # Jason's meeting must start >= 600 and end <= 975
    s.push()
    s.add(kenneth_start >= 990)
    s.add(kenneth_start >= 540 + ph_to_marina)  # arrival at Marina at 546, but earliest start is 990
    s.add(jason_start >= kenneth_end + marina_to_presidio)
    s.add(jason_start >= 600)
    s.add(jason_end <= 975)

    if s.check() == sat:
        model = s.model()
        print("Option 2: Meet Kenneth first, then Jason")
        print(f"Meet Kenneth from {model[kenneth_start].as_long()} to {model[kenneth_end].as_long()}")
        print(f"Meet Jason from {model[jason_start].as_long()} to {model[jason_end].as_long()}")
        total_time = (model[jason_end].as_long() - model[jason_start].as_long()) + (model[kenneth_end].as_long() - model[kenneth_start].as_long())
        print(f"Total time with friends: {total_time} minutes")
    else:
        print("Option 2 is not feasible")
    s.pop()

    # Determine the best option by maximizing the total time
    # Re-initialize solver for optimization
    opt = Optimize()

    # Variables
    jason_start = Int('jason_start')
    jason_end = Int('jason_end')
    kenneth_start = Int('kenneth_start')
    kenneth_end = Int('kenneth_end')

    # Constraints for Jason
    opt.add(jason_start >= 600)
    opt.add(jason_end <= 975)
    opt.add(jason_end - jason_start >= 90)

    # Constraints for Kenneth
    opt.add(kenneth_start >= 990)
    opt.add(kenneth_end <= 1005)
    opt.add(kenneth_end - kenneth_start >= 45)

    # Try both orders and find the feasible one with maximum total time
    # Order 1: Jason first
    opt.push()
    opt.add(jason_start >= 540 + ph_to_presidio)
    opt.add(kenneth_start >= jason_end + presidio_to_marina)
    opt.add(kenneth_start >= 990)
    total_time = (jason_end - jason_start) + (kenneth_end - kenneth_start)
    opt.maximize(total_time)
    if opt.check() == sat:
        model = opt.model()
        total = model.evaluate(total_time).as_long()
        print(f"Optimal solution (Jason first): Total time = {total}")
        print(f"Jason: {model[jason_start]} to {model[jason_end]}")
        print(f"Kenneth: {model[kenneth_start]} to {model[kenneth_end]}")
    else:
        print("No feasible solution for Jason first order")
    opt.pop()

    # Order 2: Kenneth first
    opt.push()
    opt.add(kenneth_start >= 540 + ph_to_marina)
    opt.add(jason_start >= kenneth_end + marina_to_presidio)
    opt.add(jason_start >= 600)
    total_time = (jason_end - jason_start) + (kenneth_end - kenneth_start)
    opt.maximize(total_time)
    if opt.check() == sat:
        model = opt.model()
        total = model.evaluate(total_time).as_long()
        print(f"Optimal solution (Kenneth first): Total time = {total}")
        print(f"Kenneth: {model[kenneth_start]} to {model[kenneth_end]}")
        print(f"Jason: {model[jason_start]} to {model[jason_end]}")
    else:
        print("No feasible solution for Kenneth first order")
    opt.pop()

solve_scheduling()