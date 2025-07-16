from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define variables for meeting times (in minutes since midnight)
    karen_start = Int('karen_start')
    karen_end = Int('karen_end')
    anthony_start = Int('anthony_start')
    anthony_end = Int('anthony_end')
    betty_start = Int('betty_start')
    betty_end = Int('betty_end')

    # Time constants (minutes since midnight)
    arrival_time = 540  # 9:00 AM
    betty_window_start = 1170  # 7:45 PM
    betty_window_end = 1305    # 9:45 PM
    karen_window_start = 525   # 8:45 AM
    karen_window_end = 900     # 3:00 PM
    anthony_window_start = 555 # 9:15 AM
    anthony_window_end = 1350  # 9:30 PM

    # Meeting duration requirements
    karen_min = 30
    anthony_min = 105
    betty_min = 15

    # Travel times (minutes)
    bayview_to_wharf = 25
    wharf_to_financial = 11
    financial_to_embarcadero = 4

    # Meeting constraints
    # Karen meeting
    s.add(karen_start >= karen_window_start)
    s.add(karen_end <= karen_window_end)
    s.add(karen_end - karen_start >= karen_min)
    s.add(karen_start >= arrival_time + bayview_to_wharf)

    # Anthony meeting
    s.add(anthony_start >= anthony_window_start)
    s.add(anthony_end <= anthony_window_end)
    s.add(anthony_end - anthony_start >= anthony_min)
    s.add(anthony_start >= karen_end + wharf_to_financial)

    # Betty meeting
    s.add(betty_start >= betty_window_start)
    s.add(betty_end <= betty_window_end)
    s.add(betty_end - betty_start >= betty_min)
    s.add(betty_start >= anthony_end + financial_to_embarcadero)

    # Check for solution
    if s.check() == sat:
        m = s.model()
        
        def format_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            ampm = "AM" if hours < 12 else "PM"
            if hours > 12:
                hours -= 12
            elif hours == 0:
                hours = 12
            return f"{hours}:{mins:02d} {ampm}"

        k_s = m[karen_start].as_long()
        k_e = m[karen_end].as_long()
        a_s = m[anthony_start].as_long()
        a_e = m[anthony_end].as_long()
        b_s = m[betty_start].as_long()
        b_e = m[betty_end].as_long()

        print("SOLUTION:")
        print(f"Meet Karen at Fisherman's Wharf from {format_time(k_s)} to {format_time(k_e)}")
        print(f"Meet Anthony at Financial District from {format_time(a_s)} to {format_time(a_e)}")
        print(f"Meet Betty at Embarcadero from {format_time(b_s)} to {format_time(b_e)}")
    else:
        print("No feasible schedule found that meets all constraints.")

solve_scheduling()