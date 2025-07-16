from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Convert all times to minutes since midnight
    arrival_time = 9 * 60  # 9:00 AM
    barbara_start = 13 * 60 + 15  # 1:15 PM
    barbara_end = 18 * 60 + 15    # 6:15 PM
    travel_time = 14  # minutes

    # Variables for meeting times
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')

    # Constraints
    # Meeting must be within Barbara's availability
    s.add(meeting_start >= barbara_start)
    s.add(meeting_end <= barbara_end)
    # Meeting duration at least 45 minutes
    s.add(meeting_end - meeting_start >= 45)
    # Must leave Russian Hill early enough to arrive by meeting start
    s.add(meeting_start - travel_time >= arrival_time)

    # Solve and format output
    if s.check() == sat:
        m = s.model()
        start = m[meeting_start].as_long()
        end = m[meeting_end].as_long()
        # Format time as HH:MM
        start_time = f"{start//60}:{start%60:02d}"
        end_time = f"{end//60}:{end%60:02d}"
        print(f"SOLUTION: Meet Barbara from {start_time} to {end_time}")
    else:
        print("No valid schedule found.")

solve_scheduling()