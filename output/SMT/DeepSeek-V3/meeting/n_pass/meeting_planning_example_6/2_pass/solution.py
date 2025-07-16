from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Convert all times to minutes since midnight
    # Kenneth's availability: 2:15 PM to 7:45 PM
    kenneth_start = 14 * 60 + 15  # 2:15 PM in minutes since midnight
    kenneth_end = 19 * 60 + 45    # 7:45 PM in minutes since midnight

    # Meeting start and end times (in minutes since midnight)
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')

    # Constraints
    s.add(meeting_start >= kenneth_start)
    s.add(meeting_end <= kenneth_end)
    s.add(meeting_end - meeting_start >= 90)  # At least 90 minutes
    s.add(meeting_start < meeting_end)

    # Travel time: 11 minutes from Fisherman's Wharf to Nob Hill
    # You arrive at Fisherman's Wharf at 9:00 AM (540 minutes since midnight)
    # Earliest you can arrive at Nob Hill is 540 + 11 = 551 minutes (9:11 AM)
    # Since Kenneth is only available from 2:15 PM, no additional constraint is needed here

    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        start = m[meeting_start].as_long()
        end = m[meeting_end].as_long()
        # Convert minutes back to time
        start_hour = start // 60
        start_min = start % 60
        end_hour = end // 60
        end_min = end % 60
        print(f"Meet Kenneth from {start_hour}:{start_min:02d} to {end_hour}:{end_min:02d}")
    else:
        print("No valid schedule found.")

solve_scheduling()