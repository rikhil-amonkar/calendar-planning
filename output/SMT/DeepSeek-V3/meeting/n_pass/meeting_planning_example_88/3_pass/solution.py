from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Time variables (in minutes since midnight)
    leave_sunset = Int('leave_sunset')            # Time you leave Sunset District
    arrive_golden_gate = Int('arrive_golden_gate') # Time you arrive at Golden Gate Park
    meet_start = Int('meet_start')                # Start time of meeting with Joshua
    meet_end = Int('meet_end')                    # End time of meeting with Joshua

    # Constraints:
    # 1. You arrive at Sunset District at 9:00 AM (540 minutes)
    s.add(leave_sunset >= 540)

    # 2. Travel time from Sunset to Golden Gate Park is 11 minutes
    s.add(arrive_golden_gate == leave_sunset + 11)

    # 3. Joshua is available from 8:45 PM (1245 minutes) to 9:45 PM (1305 minutes)
    #    Meeting must last at least 15 minutes within this window
    s.add(meet_start >= 1245)
    s.add(meet_end <= 1305)
    s.add(meet_end == meet_start + 15)

    # 4. You must arrive at Golden Gate Park before or at the meeting start time
    s.add(arrive_golden_gate <= meet_start)

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        # Convert minutes to HH:MM format
        def format_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            period = "AM" if hours < 12 else "PM"
            if hours > 12:
                hours -= 12
            return f"{hours}:{mins:02d} {period}"

        print(f"Leave Sunset District at: {format_time(m[leave_sunset].as_long())}")
        print(f"Arrive at Golden Gate Park at: {format_time(m[arrive_golden_gate].as_long())}")
        print(f"Meet Joshua from: {format_time(m[meet_start].as_long())} to {format_time(m[meet_end].as_long())}")
    else:
        print("No valid schedule exists to meet Joshua under the given constraints.")

solve_scheduling()