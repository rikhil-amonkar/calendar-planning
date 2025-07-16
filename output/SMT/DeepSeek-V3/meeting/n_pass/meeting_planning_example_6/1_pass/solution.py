from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Convert all times to minutes since 9:00 AM (540 minutes since midnight)
    # Kenneth's availability: 2:15 PM to 7:45 PM
    # 2:15 PM is 14*60 + 15 = 855 minutes since midnight, 855 - 540 = 315 minutes since 9:00 AM
    # 7:45 PM is 19*60 + 45 = 1185 minutes since midnight, 1185 - 540 = 645 minutes since 9:00 AM
    kenneth_start_min = 315  # 2:15 PM relative to 9:00 AM
    kenneth_end_min = 645    # 7:45 PM relative to 9:00 AM

    # Meeting start and end times (relative to 9:00 AM)
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')

    # Constraints
    s.add(meeting_start >= kenneth_start_min)
    s.add(meeting_end <= kenneth_end_min)
    s.add(meeting_end - meeting_start >= 90)  # At least 90 minutes
    s.add(meeting_start < meeting_end)

    # Travel time: 11 minutes from Fisherman's Wharf to Nob Hill
    # You can arrive at Nob Hill by 9:11 AM, but Kenneth is only available from 2:15 PM, so no additional constraint

    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        start = m[meeting_start].as_long()
        end = m[meeting_end].as_long()
        # Convert minutes back to time
        start_hour = (start // 60) + 9
        start_min = start % 60
        end_hour = (end // 60) + 9
        end_min = end % 60
        print(f"Meet Kenneth from {start_hour}:{start_min:02d} to {end_hour}:{end_min:02d}")
    else:
        print("No valid schedule found.")

solve_scheduling()