from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables (in minutes since 9:00 AM)
    start_kenneth = Int('start_kenneth')
    end_kenneth = Int('end_kenneth')
    start_barbara = Int('start_barbara')
    end_barbara = Int('end_barbara')

    # Travel times (minutes)
    fd_to_china = 5    # Financial District to Chinatown
    fd_to_ggp = 23      # Financial District to Golden Gate Park
    china_to_ggp = 23   # Chinatown to Golden Gate Park
    ggp_to_china = 23   # Golden Gate Park to Chinatown

    # Friend availability windows (minutes since 9:00 AM)
    kenneth_start = 180  # 12:00 PM (3 hours after 9:00 AM)
    kenneth_end = 360    # 3:00 PM (6 hours after 9:00 AM)
    barbara_start = 0     # 9:00 AM
    barbara_end = 600     # 7:00 PM (10 hours after 9:00 AM)

    # Minimum meeting durations
    min_kenneth = 90
    min_barbara = 45

    # Meeting duration constraints
    s.add(start_kenneth >= kenneth_start)
    s.add(end_kenneth <= kenneth_end)
    s.add(end_kenneth - start_kenneth >= min_kenneth)
    
    s.add(start_barbara >= barbara_start)
    s.add(end_barbara <= barbara_end)
    s.add(end_barbara - start_barbara >= min_barbara)

    # We must choose one of two sequences:
    # 1. Financial District -> Barbara -> Kenneth
    # 2. Financial District -> Kenneth -> Barbara

    # Option 1: Visit Barbara first
    option1 = And(
        start_barbara >= fd_to_ggp,  # Travel to Barbara
        start_kenneth >= end_barbara + ggp_to_china  # Travel to Kenneth
    )

    # Option 2: Visit Kenneth first
    option2 = And(
        start_kenneth >= fd_to_china,  # Travel to Kenneth
        start_barbara >= end_kenneth + china_to_ggp  # Travel to Barbara
    )

    s.add(Or(option1, option2))

    if s.check() == sat:
        m = s.model()
        
        def format_time(minutes):
            total = 540 + minutes  # 9:00 AM = 540 minutes
            h = total // 60
            m = total % 60
            ampm = "AM" if h < 12 else "PM"
            h = h if h <= 12 else h - 12
            return f"{h}:{m:02d} {ampm}"

        sk = m.eval(start_kenneth).as_long()
        ek = m.eval(end_kenneth).as_long()
        sb = m.eval(start_barbara).as_long()
        eb = m.eval(end_barbara).as_long()

        print("SOLUTION:")
        print(f"Meet Kenneth: {format_time(sk)} to {format_time(ek)}")
        print(f"Meet Barbara: {format_time(sb)} to {format_time(eb)}")
        
        # Print travel times
        if m.eval(option1):
            print("\nSchedule:")
            print(f"9:00 AM: Start at Financial District")
            print(f"9:23 AM: Arrive at Golden Gate Park (Barbara)")
            print(f"{format_time(sb)}-{format_time(eb)}: Meet Barbara")
            print(f"{format_time(eb)}: Travel to Chinatown (23 mins)")
            print(f"{format_time(sk)}-{format_time(ek)}: Meet Kenneth")
        else:
            print("\nSchedule:")
            print(f"9:00 AM: Start at Financial District")
            print(f"9:05 AM: Arrive at Chinatown (Kenneth)")
            print(f"{format_time(sk)}-{format_time(ek)}: Meet Kenneth")
            print(f"{format_time(ek)}: Travel to Golden Gate Park (23 mins)")
            print(f"{format_time(sb)}-{format_time(eb)}: Meet Barbara")
    else:
        print("No feasible schedule found")

solve_scheduling()