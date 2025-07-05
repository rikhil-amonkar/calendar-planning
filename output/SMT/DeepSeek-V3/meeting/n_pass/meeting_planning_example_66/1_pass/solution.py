from z3 import *

def solve_scheduling():
    # Create a solver instance
    s = Solver()

    # Convert times to minutes since 9:00 AM (540 minutes since midnight)
    # Robert's availability: 11:15 AM to 5:45 PM
    robert_start = (11 * 60 + 15) - (9 * 60)  # 135 minutes after 9:00 AM
    robert_end = (17 * 60 + 45) - (9 * 60)    # 525 minutes after 9:00 AM

    # Variables for meeting start and end times (relative to 9:00 AM)
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')

    # Constraints
    # Meeting must start within Robert's availability
    s.add(meeting_start >= robert_start)
    s.add(meeting_start <= robert_end - 120)  # Ensure at least 120 minutes meeting

    # Meeting must end within Robert's availability
    s.add(meeting_end >= meeting_start + 120)
    s.add(meeting_end <= robert_end)

    # Travel time to Presidio is 17 minutes, but since we start at Nob Hill at 0 minutes (9:00 AM),
    # we must arrive at Presidio by meeting_start. So, meeting_start >= 17.
    # But Robert's availability starts at 135, so this is already covered.

    # Maximize the meeting duration (which is meeting_end - meeting_start)
    # Since the minimum is 120, we can try to maximize it up to robert_end - meeting_start
    # But since the constraints enforce at least 120, any solution meeting that is acceptable.
    # However, to get the maximum possible meeting time, we can set the objective to maximize (meeting_end - meeting_start)
    # But since the problem asks to meet for at least 120 minutes, and doesn't specify to maximize beyond that,
    # we can just find any solution meeting the constraints.

    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        start = m[meeting_start].as_long()
        end = m[meeting_end].as_long()
        duration = end - start

        # Convert back to time strings
        def to_time(minutes):
            total_minutes = 9 * 60 + minutes
            hours = total_minutes // 60
            mins = total_minutes % 60
            return f"{hours}:{mins:02d}"

        start_time = to_time(start)
        end_time = to_time(end)
        print(f"SOLUTION: Meet Robert from {start_time} to {end_time} (duration: {duration} minutes)")
    else:
        print("No valid schedule found.")

solve_scheduling()