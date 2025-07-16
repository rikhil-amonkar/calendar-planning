from z3 import *

def solve_scheduling():
    # Create a solver instance
    s = Solver()

    # Variables for the schedule
    leave_golden_gate = Int('leave_golden_gate')  # Time in minutes from 9:00 AM
    arrive_chinatown = Int('arrive_chinatown')    # Time in minutes from 9:00 AM
    leave_chinatown = Int('leave_chinatown')      # Time in minutes from 9:00 AM

    # Convert all times to minutes since 9:00 AM
    david_start = (16 * 60) - (9 * 60)  # 4:00 PM is 16:00, so 16*60 - 9*60 = 420 minutes
    david_end = (21 * 60 + 45) - (9 * 60)  # 9:45 PM is 21:45, so 21*60+45 - 9*60 = 765 minutes
    travel_time = 23  # minutes

    # Constraints
    s.add(leave_golden_gate >= 0)  # You can't leave before 9:00 AM
    s.add(arrive_chinatown == leave_golden_gate + travel_time)
    s.add(leave_chinatown == arrive_chinatown + 105)  # Meet for 105 minutes
    s.add(arrive_chinatown >= david_start)
    s.add(leave_chinatown <= david_end)

    # Objective: maximize the time spent with David (which is fixed at 105 minutes, so any solution is acceptable)
    # Since the meeting duration is fixed, we just need to find a feasible solution

    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        leave_gg = m[leave_golden_gate].as_long()
        arrive_ct = m[arrive_chinatown].as_long()
        leave_ct = m[leave_chinatown].as_long()

        # Convert minutes back to time format
        def minutes_to_time(minutes):
            hours = 9 + (minutes // 60)
            mins = minutes % 60
            return f"{hours}:{mins:02d}"

        leave_gg_time = minutes_to_time(leave_gg)
        arrive_ct_time = minutes_to_time(arrive_ct)
        leave_ct_time = minutes_to_time(leave_ct)

        print(f"Leave Golden Gate Park at: {leave_gg_time}")
        print(f"Arrive in Chinatown at: {arrive_ct_time}")
        print(f"Leave Chinatown at: {leave_ct_time}")
    else:
        print("No feasible schedule found.")

solve_scheduling()