from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define locations
    FW = 0  # Fisherman's Wharf
    GGP = 1  # Golden Gate Park
    PR = 2   # Presidio
    RD = 3   # Richmond District

    # Travel times in minutes (from, to): time
    travel = {
        (FW, GGP): 25,
        (FW, PR): 17,
        (FW, RD): 18,
        (GGP, FW): 24,
        (GGP, PR): 11,
        (GGP, RD): 7,
        (PR, FW): 19,
        (PR, GGP): 12,
        (PR, RD): 7,
        (RD, FW): 18,
        (RD, GGP): 9,
        (RD, PR): 7
    }

    # Time variables (in minutes since midnight)
    melissa_start = Int('melissa_start')
    melissa_end = Int('melissa_end')
    nancy_start = Int('nancy_start')
    nancy_end = Int('nancy_end')
    emily_start = Int('emily_start')
    emily_end = Int('emily_end')

    # Meeting duration constraints
    s.add(melissa_end - melissa_start >= 15)  # Melissa: min 15 mins
    s.add(nancy_end - nancy_start >= 105)     # Nancy: min 105 mins
    s.add(emily_end - emily_start >= 120)     # Emily: min 120 mins

    # Availability windows
    s.add(melissa_start >= 510)   # 8:30 AM (510 mins)
    s.add(melissa_end <= 1200)    # 8:00 PM (1200 mins)
    s.add(nancy_start >= 1185)    # 7:45 PM (1185 mins)
    s.add(nancy_end <= 1320)      # 10:00 PM (1320 mins)
    s.add(emily_start >= 1065)    # 4:45 PM (1065 mins)
    s.add(emily_end <= 1320)      # 10:00 PM (1320 mins)

    # Starting at Fisherman's Wharf at 9:00 AM (540 mins)
    current_time = 540
    current_loc = FW

    # Meet Melissa at Golden Gate Park
    travel_time = travel[(current_loc, GGP)]
    arrive_melissa = current_time + travel_time
    s.add(melissa_start >= arrive_melissa)
    leave_melissa = melissa_end
    current_loc = GGP

    # Meet Emily at Richmond District
    travel_time = travel[(current_loc, RD)]
    arrive_emily = leave_melissa + travel_time
    s.add(emily_start >= arrive_emily)
    leave_emily = emily_end
    current_loc = RD

    # Meet Nancy at Presidio
    travel_time = travel[(current_loc, PR)]
    arrive_nancy = leave_emily + travel_time
    s.add(nancy_start >= arrive_nancy)

    # Check for a valid schedule
    if s.check() == sat:
        m = s.model()
        print("Valid schedule found:")
        print(f"Melissa: {m[melissa_start].as_long()//60}:{m[melissa_start].as_long()%60:02d} to {m[melissa_end].as_long()//60}:{m[melissa_end].as_long()%60:02d} at Golden Gate Park")
        print(f"Emily: {m[emily_start].as_long()//60}:{m[emily_start].as_long()%60:02d} to {m[emily_end].as_long()//60}:{m[emily_end].as_long()%60:02d} at Richmond District")
        print(f"Nancy: {m[nancy_start].as_long()//60}:{m[nancy_start].as_long()%60:02d} to {m[nancy_end].as_long()//60}:{m[nancy_end].as_long()%60:02d} at Presidio")
    else:
        print("No valid schedule exists that meets all constraints.")

solve_scheduling()