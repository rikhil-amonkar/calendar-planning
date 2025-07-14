from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Convert all times to minutes since midnight
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

    # Variables for meeting start and end times
    jason_start = Int('jason_start')
    jason_end = Int('jason_end')
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

    # Starting at Pacific Heights at 9:00 AM (540 minutes)
    # Option 1: Meet Jason first, then Kenneth
    s.push()
    # Travel to Presidio: 11 minutes
    arrival_presidio = 540 + ph_to_presidio  # 551
    # Can't meet Jason before 10:00 AM (600)
    s.add(jason_start >= max(arrival_presidio, jason_start_min))
    # Travel to Marina after meeting Jason
    arrival_marina = jason_end + presidio_to_marina
    # Can't meet Kenneth before 3:30 PM (990)
    s.add(kenneth_start >= max(arrival_marina, kenneth_start_min))
    s.add(kenneth_end <= kenneth_end_max)

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
    s.push()
    # Travel to Marina: 6 minutes
    arrival_marina = 540 + ph_to_marina  # 546
    # Can't meet Kenneth before 3:30 PM (990)
    s.add(kenneth_start >= max(arrival_marina, kenneth_start_min))
    # Travel to Presidio after meeting Kenneth
    arrival_presidio = kenneth_end + marina_to_presidio
    # Can't meet Jason before 10:00 AM (600)
    s.add(jason_start >= max(arrival_presidio, jason_start_min))
    s.add(jason_end <= jason_end_max)

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

    # If both options are not feasible, try adjusting meeting durations
    s = Solver()

    # Variables
    jason_start = Int('jason_start')
    jason_end = Int('jason_end')
    kenneth_start = Int('kenneth_start')
    kenneth_end = Int('kenneth_end')

    # Minimum meeting durations
    s.add(jason_end - jason_start >= 90)
    s.add(kenneth_end - kenneth_start >= 45)

    # Option 1: Meet Jason first
    s.push()
    s.add(jason_start >= max(540 + ph_to_presidio, 600))
    s.add(jason_end <= 975)
    s.add(kenneth_start >= max(jason_end + presidio_to_marina, 990))
    s.add(kenneth_end <= 1005)

    if s.check() == sat:
        model = s.model()
        print("Adjusted Option 1: Meet Jason first, then Kenneth")
        print(f"Meet Jason from {model[jason_start].as_long()} to {model[jason_end].as_long()}")
        print(f"Meet Kenneth from {model[kenneth_start].as_long()} to {model[kenneth_end].as_long()}")
    else:
        print("Adjusted Option 1 is not feasible")
    s.pop()

    # Option 2: Meet Kenneth first
    s.push()
    s.add(kenneth_start >= max(540 + ph_to_marina, 990))
    s.add(kenneth_end <= 1005)
    s.add(jason_start >= max(kenneth_end + marina_to_presidio, 600))
    s.add(jason_end <= 975)

    if s.check() == sat:
        model = s.model()
        print("Adjusted Option 2: Meet Kenneth first, then Jason")
        print(f"Meet Kenneth from {model[kenneth_start].as_long()} to {model[kenneth_end].as_long()}")
        print(f"Meet Jason from {model[jason_start].as_long()} to {model[jason_end].as_long()}")
    else:
        print("Adjusted Option 2 is not feasible")
    s.pop()

solve_scheduling()