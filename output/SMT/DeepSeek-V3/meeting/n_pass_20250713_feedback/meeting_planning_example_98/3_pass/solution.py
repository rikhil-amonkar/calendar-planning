from z3 import *

def solve_scheduling():
    # Create a solver instance
    s = Solver()
    
    # Variables representing the start and end times of the meeting with Timothy
    # All times are in minutes since 9:00 AM (0 minutes = 9:00 AM)
    meet_start = Int('meet_start')
    meet_end = Int('meet_end')
    
    # Timothy's availability window (in minutes since 9:00 AM)
    timothy_start = (12 * 60 + 45) - (9 * 60)  # 8:45 PM is 11 hours and 45 minutes after 9:00 AM
    timothy_end = (12 * 60 + 30) - (9 * 60)    # 9:30 PM is 12 hours and 30 minutes after 9:00 AM
    
    # Travel times
    travel_to_richmond = 12  # minutes
    travel_to_alamo = 13     # minutes
    
    # Constraints:
    # 1. Meeting must be within Timothy's availability
    s.add(meet_start >= timothy_start)
    s.add(meet_end <= timothy_end)
    
    # 2. Meeting duration must be at least 45 minutes
    s.add(meet_end - meet_start >= 45)
    
    # 3. You must leave Alamo Square early enough to arrive at Richmond by meet_start
    leave_alamo = meet_start - travel_to_richmond
    s.add(leave_alamo >= 0)  # Cannot leave before 9:00 AM (0 minutes)
    
    # 4. You return to Alamo Square after the meeting
    return_alamo = meet_end + travel_to_alamo
    
    # 5. No other meetings are scheduled (only meet Timothy)
    # This is implicitly enforced by not scheduling any other meetings
    
    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        print("Solution found:")
        print(f"Leave Alamo Square at: {m[leave_alamo].as_long()} minutes after 9:00 AM")
        print(f"Meet Timothy from: {m[meet_start].as_long()} to {m[meet_end].as_long()} minutes after 9:00 AM")
        print(f"Return to Alamo Square at: {m[return_alamo].as_long()} minutes after 9:00 AM")
    else:
        print("No feasible schedule found.")

solve_scheduling()