from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define the work hours (9:00 to 17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes

    # Meeting duration is 30 minutes
    meeting_duration = 30

    # Possible start times for the meeting (in minutes from 0:00)
    start_time = Int('start_time')
    s.add(start_time >= work_start)
    s.add(start_time + meeting_duration <= work_end)

    # Evelyn has no meetings, but doesn't want to meet after 13:00
    evelyn_constraint = (start_time + meeting_duration <= 13 * 60)
    s.add(evelyn_constraint)

    # Randy's busy times (in minutes from 0:00)
    randy_busy = [
        (9 * 60, 10 * 60 + 30),   # 9:00 to 10:30
        (11 * 60, 15 * 60 + 30),  # 11:00 to 15:30
        (16 * 60, 17 * 60)        # 16:00 to 17:00
    ]

    # Add constraints that the meeting does not overlap with Randy's busy times
    for busy_start, busy_end in randy_busy:
        s.add(Or(
            start_time + meeting_duration <= busy_start,
            start_time >= busy_end
        ))

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        start_min = m[start_time].as_long()
        start_hour = start_min // 60
        start_min = start_min % 60
        end_min = start_min + meeting_duration
        end_hour = start_hour + (end_min // 60)
        end_min = end_min % 60

        # Format the output
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_hour:02d}:{start_min:02d}")
        print(f"End Time: {end_hour:02d}:{end_min:02d}")
    else:
        print("No solution found")

solve_scheduling()