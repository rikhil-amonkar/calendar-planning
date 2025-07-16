from z3 import *

def solve_scheduling():
    # Initialize solver
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

    # Create time variables (minutes since midnight)
    melissa_start = Int('melissa_start')
    melissa_end = Int('melissa_end')
    nancy_start = Int('nancy_start')
    nancy_end = Int('nancy_end')
    emily_start = Int('emily_start')
    emily_end = Int('emily_end')

    # Meeting duration constraints
    s.add(melissa_end - melissa_start >= 15)
    s.add(nancy_end - nancy_start >= 105)
    s.add(emily_end - emily_start >= 120)

    # Availability windows
    s.add(melissa_start >= 510)   # 8:30 AM
    s.add(melissa_end <= 1200)    # 8:00 PM
    s.add(nancy_start >= 1185)    # 7:45 PM
    s.add(nancy_end <= 1320)      # 10:00 PM
    s.add(emily_start >= 1065)    # 4:45 PM
    s.add(emily_end <= 1320)      # 10:00 PM

    # Starting point
    current_time = 540  # 9:00 AM at Fisherman's Wharf
    current_loc = FW

    # Schedule Melissa meeting
    travel_time = travel[(current_loc, GGP)]
    arrive_melissa = current_time + travel_time
    s.add(melissa_start >= arrive_melissa)
    leave_melissa = melissa_end
    current_loc = GGP

    # Schedule Emily meeting
    travel_time = travel[(current_loc, RD)]
    arrive_emily = leave_melissa + travel_time
    s.add(emily_start >= arrive_emily)
    leave_emily = emily_end
    current_loc = RD

    # Schedule Nancy meeting
    travel_time = travel[(current_loc, PR)]
    arrive_nancy = leave_emily + travel_time
    s.add(nancy_start >= arrive_nancy)

    # Check for solution
    if s.check() == sat:
        m = s.model()
        print("\nOptimal Schedule Found:")
        
        def format_time(minutes):
            return f"{minutes//60}:{minutes%60:02d}"
        
        print(f"1. Meet Melissa at Golden Gate Park: {format_time(m[melissa_start].as_long())} to {format_time(m[melissa_end].as_long())}")
        print(f"   - Travel time from Fisherman's Wharf: 25 minutes")
        
        print(f"2. Meet Emily at Richmond District: {format_time(m[emily_start].as_long())} to {format_time(m[emily_end].as_long())}")
        print(f"   - Travel time from Golden Gate Park: 7 minutes")
        
        print(f"3. Meet Nancy at Presidio: {format_time(m[nancy_start].as_long())} to {format_time(m[nancy_end].as_long())}")
        print(f"   - Travel time from Richmond District: 7 minutes")
        
        total_meeting_time = (m[melissa_end].as_long() - m[melissa_start].as_long()) + \
                            (m[emily_end].as_long() - m[emily_start].as_long()) + \
                            (m[nancy_end].as_long() - m[nancy_start].as_long())
        print(f"\nTotal Meeting Time: {total_meeting_time} minutes")
    else:
        print("No valid schedule exists that meets all constraints.")

solve_scheduling()