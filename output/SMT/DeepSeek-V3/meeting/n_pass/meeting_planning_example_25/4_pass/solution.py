from z3 import *

def solve_scheduling():
    # Create solver instance
    s = Solver()

    # Define variables (minutes since 9:00 AM)
    leave_park = Int('leave_park')  # When to leave Golden Gate Park
    arrive_china = Int('arrive_china')  # When to arrive in Chinatown
    leave_china = Int('leave_china')  # When to leave Chinatown

    # Convert time constraints to minutes since 9:00 AM
    david_start = (16 * 60)  # 4:00 PM = 16:00 = 960 minutes since midnight - 540 = 420
    david_end = (21 * 60 + 45)  # 9:45 PM = 21:45 = 1305 minutes since midnight - 540 = 765
    travel_time = 23  # minutes

    # Add constraints
    s.add(leave_park >= 0)  # Can't leave before 9:00 AM
    s.add(arrive_china == leave_park + travel_time)
    s.add(leave_china == arrive_china + 105)  # Meet for 105 minutes
    s.add(arrive_china >= david_start)
    s.add(leave_china <= david_end)

    # Check for solution
    if s.check() == sat:
        m = s.model()
        # Get values
        leave_park_val = m[leave_park].as_long()
        arrive_china_val = m[arrive_china].as_long()
        leave_china_val = m[leave_china].as_long()

        # Convert minutes to time strings
        def format_time(minutes):
            total_min = 540 + minutes  # 9:00 AM = 540 minutes
            h = total_min // 60
            m = total_min % 60
            return f"{h}:{m:02d}"

        print("Optimal Schedule:")
        print(f"Leave Golden Gate Park at: {format_time(leave_park_val)}")
        print(f"Arrive in Chinatown at: {format_time(arrive_china_val)}")
        print(f"Leave Chinatown at: {format_time(leave_china_val)}")
    else:
        print("No valid schedule found that meets all constraints.")

solve_scheduling()