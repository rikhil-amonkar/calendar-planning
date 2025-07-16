from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables (in minutes since 9:00 AM)
    start_k = Int('start_k')  # Meeting with Kenneth
    end_k = Int('end_k')
    start_b = Int('start_b')  # Meeting with Barbara
    end_b = Int('end_b')

    # Travel times (minutes)
    FD_to_China = 5
    FD_to_GGP = 23
    China_to_GGP = 23
    GGP_to_China = 23

    # Availability windows (minutes since 9:00 AM)
    ken_start = 180  # 12:00 PM
    ken_end = 360    # 3:00 PM
    barb_start = 0   # 9:00 AM
    barb_end = 600   # 7:00 PM

    # Minimum durations
    min_ken = 90
    min_barb = 45

    # Meeting duration constraints
    s.add(start_k >= ken_start)
    s.add(end_k <= ken_end)
    s.add(end_k - start_k >= min_ken)
    
    s.add(start_b >= barb_start)
    s.add(end_b <= barb_end)
    s.add(end_b - start_b >= min_barb)

    # Create two options for meeting sequence
    option1 = And(  # Barbara first, then Kenneth
        start_b >= FD_to_GGP,
        start_k >= end_b + GGP_to_China
    )

    option2 = And(  # Kenneth first, then Barbara
        start_k >= FD_to_China,
        start_b >= end_k + China_to_GGP
    )

    s.add(Or(option1, option2))

    if s.check() == sat:
        m = s.model()
        
        def format_time(mins):
            total = 540 + mins  # 9:00 AM = 540 minutes
            h = total // 60
            m = total % 60
            ampm = "AM" if h < 12 else "PM"
            h = h if h <= 12 else h - 12
            return f"{h}:{m:02d} {ampm}"

        sk = m.eval(start_k).as_long()
        ek = m.eval(end_k).as_long()
        sb = m.eval(start_b).as_long()
        eb = m.eval(end_b).as_long()

        print("SOLUTION:")
        if m.eval(option1):
            print("1. Meet Barbara first:")
            print(f"  - Leave FD at 9:00 AM")
            print(f"  - Arrive GGP at {format_time(FD_to_GGP)}")
            print(f"  - Meet Barbara: {format_time(sb)} to {format_time(eb)}")
            print(f"  - Travel to Chinatown (23 mins)")
            print(f"  - Meet Kenneth: {format_time(sk)} to {format_time(ek)}")
        else:
            print("2. Meet Kenneth first:")
            print(f"  - Leave FD at 9:00 AM")
            print(f"  - Arrive Chinatown at {format_time(FD_to_China)}")
            print(f"  - Meet Kenneth: {format_time(sk)} to {format_time(ek)}")
            print(f"  - Travel to GGP (23 mins)")
            print(f"  - Meet Barbara: {format_time(sb)} to {format_time(eb)}")
    else:
        print("No feasible schedule found")

solve_scheduling()