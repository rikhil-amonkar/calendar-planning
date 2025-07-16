from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Time variables (in minutes since midnight)
    leave_sunset = Int('leave_sunset')
    arrive_golden_gate = Int('arrive_golden_gate')
    meet_start = Int('meet_start')
    meet_end = Int('meet_end')

    # Constraints:
    # 1. Arrive at Sunset District at 9:00 AM (540 minutes)
    s.add(leave_sunset >= 540)

    # 2. Travel time is 11 minutes
    s.add(arrive_golden_gate == leave_sunset + 11)

    # 3. Joshua's availability window (1245 to 1305 minutes)
    s.add(meet_start >= 1245)  # 8:45 PM
    s.add(meet_end <= 1305)    # 9:45 PM
    s.add(meet_end == meet_start + 15)  # 15 minute meeting

    # 4. Must arrive before meeting starts
    s.add(arrive_golden_gate <= meet_start)

    # Check solution
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        
        def format_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            period = "AM" if hours < 12 else "PM"
            if hours > 12:
                hours -= 12
            elif hours == 0:
                hours = 12
            return f"{hours}:{mins:02d} {period}"

        leave_time = m[leave_sunset].as_long()
        arrive_time = m[arrive_golden_gate].as_long()
        start_time = m[meet_start].as_long()
        end_time = m[meet_end].as_long()

        print(f"Leave Sunset District at: {format_time(leave_time)}")
        print(f"Arrive at Golden Gate Park at: {format_time(arrive_time)}")
        print(f"Meet Joshua from: {format_time(start_time)} to {format_time(end_time)}")
    else:
        print("No valid schedule exists to meet Joshua under the given constraints.")

solve_scheduling()