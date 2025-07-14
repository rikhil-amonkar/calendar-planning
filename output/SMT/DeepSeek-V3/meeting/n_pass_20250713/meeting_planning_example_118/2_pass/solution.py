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
    
    # We can only meet one friend, so we need to choose between Richard or Charles
    # Let's create a variable to decide which friend to meet
    meet_richard = Bool('meet_richard')
    meet_charles = Bool('meet_charles')
    
    # Ensure we meet exactly one friend
    s.add(Or(And(meet_richard, Not(meet_charles)), And(Not(meet_richard), meet_charles)))
    
    # If we meet Richard, we must travel from Bayview to Union Square
    s.add(Implies(meet_richard, richard_start >= arrival_time + bayview_to_union))
    
    # If we meet Charles, we must travel from Bayview to Presidio
    s.add(Implies(meet_charles, charles_start >= arrival_time + bayview_to_presidio))
    
    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        # Convert minutes back to time strings
        def minutes_to_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h}:{m:02d}"
        
        if m.evaluate(meet_richard):
            richard_start_time = m.evaluate(richard_start).as_long()
            richard_end_time = m.evaluate(richard_end).as_long()
            print("SOLUTION:")
            print(f"Meet Richard from {minutes_to_time(richard_start_time)} to {minutes_to_time(richard_end_time)}")
        else:
            charles_start_time = m.evaluate(charles_start).as_long()
            charles_end_time = m.evaluate(charles_end).as_long()
            print("SOLUTION:")
            print(f"Meet Charles from {minutes_to_time(charles_start_time)} to {minutes_to_time(charles_end_time)}")
    else:
        print("No feasible schedule found")

solve_scheduling()