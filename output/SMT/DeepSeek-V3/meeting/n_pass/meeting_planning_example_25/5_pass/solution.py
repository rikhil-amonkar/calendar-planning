from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables (minutes since midnight)
    leave_park = Int('leave_park')  # Departure from Golden Gate Park
    arrive_china = Int('arrive_china')  # Arrival in Chinatown
    leave_china = Int('leave_china')  # Departure from Chinatown

    # Time constants (minutes since midnight)
    start_time = 9 * 60  # 9:00 AM
    david_start = 16 * 60  # 4:00 PM
    david_end = 21 * 60 + 45  # 9:45 PM
    travel_time = 23  # minutes

    # Add constraints
    s.add(leave_park >= start_time)  # Can't leave before 9:00 AM
    s.add(arrive_china == leave_park + travel_time)
    s.add(leave_china == arrive_china + 105)  # Minimum 105 minute meeting
    s.add(arrive_china >= david_start)  # Must arrive during David's availability
    s.add(leave_china <= david_end)  # Must leave before David leaves

    # Check for solution
    if s.check() == sat:
        m = s.model()
        # Get values
        lp = m[leave_park].as_long()
        ac = m[arrive_china].as_long()
        lc = m[leave_china].as_long()

        # Convert minutes to HH:MM format
        def format_time(mins):
            return f"{mins//60}:{mins%60:02d}"

        print("Optimal Schedule:")
        print(f"Leave Golden Gate Park at: {format_time(lp)}")
        print(f"Arrive in Chinatown at: {format_time(ac)}")
        print(f"Leave Chinatown at: {format_time(lc)}")
    else:
        print("No valid schedule found that meets all constraints.")

solve_scheduling()