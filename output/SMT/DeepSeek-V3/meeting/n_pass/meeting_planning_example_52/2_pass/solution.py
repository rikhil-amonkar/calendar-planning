from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Convert times to minutes since midnight
    # Barbara's availability: 1:15 PM to 6:15 PM (795 to 1110 minutes since midnight)
    barbara_start = (13 * 60) + 15  # 1:15 PM in minutes since midnight
    barbara_end = (18 * 60) + 15    # 6:15 PM in minutes since midnight

    # Variables for meeting start and end times (in minutes since midnight)
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')

    # Constraints
    # Meeting must start and end within Barbara's availability
    s.add(meeting_start >= barbara_start)
    s.add(meeting_end <= barbara_end)
    # Meeting duration must be at least 45 minutes
    s.add(meeting_end - meeting_start >= 45)
    # You arrive at Russian Hill at 9:00 AM (540 minutes since midnight)
    # Travel time to Richmond District is 14 minutes
    # So you must leave Russian Hill at meeting_start - 14
    # Since you can't leave before 9:00 AM (540)
    s.add(meeting_start - 14 >= 540)

    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        start = m[meeting_start].as_long()
        end = m[meeting_end].as_long()
        # Convert minutes back to time strings
        start_hour = start // 60
        start_min = start % 60
        end_hour = end // 60
        end_min = end % 60
        print(f"SOLUTION: Meet Barbara from {start_hour}:{start_min:02d} to {end_hour}:{end_min:02d}")
    else:
        print("No valid schedule found.")

solve_scheduling()