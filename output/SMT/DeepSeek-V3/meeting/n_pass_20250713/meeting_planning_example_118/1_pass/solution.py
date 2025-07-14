from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define variables
    # Start and end times for meeting Richard (Union Square)
    richard_start = Int('richard_start')
    richard_end = Int('richard_end')
    
    # Start and end times for meeting Charles (Presidio)
    charles_start = Int('charles_start')
    charles_end = Int('charles_end')
    
    # Arrival time at Bayview is 9:00 AM (540 minutes since midnight)
    arrival_time = 540
    
    # Convert friends' availability to minutes since midnight
    richard_available_start = 8 * 60 + 45  # 8:45 AM
    richard_available_end = 13 * 60       # 1:00 PM
    charles_available_start = 9 * 60 + 45 # 9:45 AM
    charles_available_end = 13 * 60       # 1:00 PM
    
    # Travel times in minutes
    bayview_to_union = 17
    bayview_to_presidio = 31
    union_to_bayview = 15
    union_to_presidio = 24
    presidio_to_bayview = 31
    presidio_to_union = 22
    
    # Constraints for Richard
    s.add(richard_start >= richard_available_start)
    s.add(richard_end <= richard_available_end)
    s.add(richard_end - richard_start >= 120)  # At least 120 minutes
    
    # Constraints for Charles
    s.add(charles_start >= charles_available_start)
    s.add(charles_end <= charles_available_end)
    s.add(charles_end - charles_start >= 120)  # At least 120 minutes
    
    # Possible schedules:
    # Option 1: Meet Richard first, then Charles
    # Option 2: Meet Charles first, then Richard
    
    # We need to model both options and let the solver choose the feasible one
    
    # Option 1: Richard first, then Charles
    option1 = And(
        richard_start >= arrival_time + bayview_to_union,  # Travel from Bayview to Union Square
        charles_start >= richard_end + union_to_presidio   # Travel from Union Square to Presidio
    )
    
    # Option 2: Charles first, then Richard
    option2 = And(
        charles_start >= arrival_time + bayview_to_presidio,  # Travel from Bayview to Presidio
        richard_start >= charles_end + presidio_to_union      # Travel from Presidio to Union Square
    )
    
    # At least one of the options must be true
    s.add(Or(option1, option2))
    
    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        # Convert minutes back to time strings
        def minutes_to_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h}:{m:02d}"
        
        richard_start_time = m.evaluate(richard_start).as_long()
        richard_end_time = m.evaluate(richard_end).as_long()
        charles_start_time = m.evaluate(charles_start).as_long()
        charles_end_time = m.evaluate(charles_end).as_long()
        
        print("SOLUTION:")
        print(f"Meet Richard from {minutes_to_time(richard_start_time)} to {minutes_to_time(richard_end_time)}")
        print(f"Meet Charles from {minutes_to_time(charles_start_time)} to {minutes_to_time(charles_end_time)}")
        
        # Determine the order of meetings
        if m.evaluate(option1):
            print("Order: Richard first, then Charles")
        else:
            print("Order: Charles first, then Richard")
    else:
        print("No feasible schedule found")

solve_scheduling()