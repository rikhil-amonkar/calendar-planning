from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for each meeting's start and end times
    # Meeting with Jason at Fisherman's Wharf
    jason_start = Real('jason_start')
    jason_end = Real('jason_end')
    
    # Meeting with Jessica at Embarcadero
    jessica_start = Real('jessica_start')
    jessica_end = Real('jessica_end')
    
    # Meeting with Sandra at Richmond District
    sandra_start = Real('sandra_start')
    sandra_end = Real('sandra_end')

    # Define travel times (in minutes) from the problem statement
    bayview_to_fisherman = 25
    fisherman_to_embarcadero = 8
    embarcadero_to_richmond = 21

    # Convert all times to minutes since 9:00 AM (540 minutes)
    start_time = 540  # 9:00 AM in minutes

    # Jason's availability: 4:00 PM to 4:45 PM (960 to 1005 minutes)
    jason_available_start = 960
    jason_available_end = 1005
    # Jessica's availability: 4:45 PM to 7:00 PM (1005 to 1140 minutes)
    jessica_available_start = 1005
    jessica_available_end = 1140
    # Sandra's availability: 6:30 PM to 9:45 PM (1170 to 1305 minutes)
    sandra_available_start = 1170
    sandra_available_end = 1305

    # Constraints for Jason's meeting
    s.add(jason_start >= jason_available_start)
    s.add(jason_end <= jason_available_end)
    s.add(jason_end - jason_start >= 30)  # Minimum 30 minutes

    # Constraints for Jessica's meeting
    s.add(jessica_start >= jessica_available_start)
    s.add(jessica_end <= jessica_available_end)
    s.add(jessica_end - jessica_start >= 30)  # Minimum 30 minutes

    # Constraints for Sandra's meeting
    s.add(sandra_start >= sandra_available_start)
    s.add(sandra_end <= sandra_available_end)
    s.add(sandra_end - sandra_start >= 120)  # Minimum 120 minutes

    # Assume we start at Bayview at 9:00 AM (540 minutes)
    # Travel from Bayview to Fisherman's Wharf: 25 minutes
    s.add(jason_start >= start_time + bayview_to_fisherman)
    # Travel from Fisherman's Wharf to Embarcadero: 8 minutes
    s.add(jessica_start >= jason_end + fisherman_to_embarcadero)
    # Travel from Embarcadero to Richmond District: 21 minutes
    s.add(sandra_start >= jessica_end + embarcadero_to_richmond)

    # Check if the model is satisfiable
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        
        def minutes_to_time(minutes):
            total_minutes = 540 + float(minutes.as_decimal(2))
            hours = int(total_minutes // 60)
            minutes = int(total_minutes % 60)
            period = "AM" if hours < 12 else "PM"
            if hours > 12:
                hours -= 12
            elif hours == 0:
                hours = 12
            return f"{hours}:{minutes:02d} {period}"

        print("Meeting with Jason at Fisherman's Wharf:")
        print(f"Start: {minutes_to_time(m[jason_start])}")
        print(f"End: {minutes_to_time(m[jason_end])}")
        
        print("\nMeeting with Jessica at Embarcadero:")
        print(f"Start: {minutes_to_time(m[jessica_start])}")
        print(f"End: {minutes_to_time(m[jessica_end])}")
        
        print("\nMeeting with Sandra at Richmond District:")
        print(f"Start: {minutes_to_time(m[sandra_start])}")
        print(f"End: {minutes_to_time(m[sandra_end])}")
    else:
        print("No feasible schedule found.")

solve_scheduling()