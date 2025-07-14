from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for each meeting's start and end times
    jason_start = Real('jason_start')
    jason_end = Real('jason_end')
    jessica_start = Real('jessica_start')
    jessica_end = Real('jessica_end')
    sandra_start = Real('sandra_start')
    sandra_end = Real('sandra_end')

    # Travel times in minutes
    bayview_to_fisherman = 25
    fisherman_to_embarcadero = 8
    embarcadero_to_richmond = 21

    # Convert all times to minutes since 9:00 AM (540 minutes)
    start_time = 540  # 9:00 AM in minutes

    # Friends' availability windows
    jason_window = (960, 1005)    # 4:00 PM - 4:45 PM
    jessica_window = (1005, 1140) # 4:45 PM - 7:00 PM
    sandra_window = (1170, 1305)  # 6:30 PM - 9:45 PM

    # Meeting duration constraints
    s.add(jason_end - jason_start >= 30)    # Jason: 30 min
    s.add(jessica_end - jessica_start >= 30) # Jessica: 30 min
    s.add(sandra_end - sandra_start >= 120) # Sandra: 120 min

    # Availability constraints
    s.add(jason_start >= jason_window[0])
    s.add(jason_end <= jason_window[1])
    s.add(jessica_start >= jessica_window[0])
    s.add(jessica_end <= jessica_window[1])
    s.add(sandra_start >= sandra_window[0])
    s.add(sandra_end <= sandra_window[1])

    # Travel constraints
    # From Bayview (start) to Fisherman's Wharf (Jason)
    s.add(jason_start >= start_time + bayview_to_fisherman)
    # From Fisherman's Wharf to Embarcadero (Jessica)
    s.add(jessica_start >= jason_end + fisherman_to_embarcadero)
    # From Embarcadero to Richmond District (Sandra)
    s.add(sandra_start >= jessica_end + embarcadero_to_richmond)

    # Check if schedule is possible
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        
        def format_time(minutes):
            total = 540 + float(m[minutes].as_decimal(2))
            hours = int(total // 60)
            mins = int(total % 60)
            period = "PM" if hours >= 12 else "AM"
            if hours > 12: hours -= 12
            return f"{hours}:{mins:02d} {period}"

        print("Meeting with Jason at Fisherman's Wharf:")
        print(f"Start: {format_time(jason_start)}")
        print(f"End: {format_time(jason_end)}")
        
        print("\nMeeting with Jessica at Embarcadero:")
        print(f"Start: {format_time(jessica_start)}")
        print(f"End: {format_time(jessica_end)}")
        
        print("\nMeeting with Sandra at Richmond District:")
        print(f"Start: {format_time(sandra_start)}")
        print(f"End: {format_time(sandra_end)}")
    else:
        print("No feasible schedule found that meets all constraints.")

solve_scheduling()