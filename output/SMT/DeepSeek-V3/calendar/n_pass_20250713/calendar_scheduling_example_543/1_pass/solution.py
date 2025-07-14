from z3 import *

def solve_scheduling():
    # Define the work hours (9:00 to 17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    meeting_duration = 60  # 1 hour in minutes

    # Define the busy slots for James and John in minutes since midnight
    james_busy = [
        (11 * 60 + 30, 12 * 60),      # 11:30-12:00
        (14 * 60 + 30, 15 * 60)       # 14:30-15:00
    ]
    john_busy = [
        (9 * 60 + 30, 11 * 60),       # 9:30-11:00
        (11 * 60 + 30, 12 * 60),      # 11:30-12:00
        (12 * 60 + 30, 13 * 60 + 30), # 12:30-13:30
        (14 * 60 + 30, 16 * 60 + 30)  # 14:30-16:30
    ]

    # Create a Z3 solver instance
    s = Solver()

    # Define the start time of the meeting (in minutes since midnight)
    start_time = Int('start_time')

    # Constraint: Meeting must start within work hours and end before work ends
    s.add(start_time >= work_start)
    s.add(start_time + meeting_duration <= work_end)

    # Constraint: Meeting must not overlap with James's busy slots
    for busy_start, busy_end in james_busy:
        s.add(Or(
            start_time + meeting_duration <= busy_start,
            start_time >= busy_end
        ))

    # Constraint: Meeting must not overlap with John's busy slots
    for busy_start, busy_end in john_busy:
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

        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_hour:02d}:{start_min:02d}")
        print(f"End Time: {end_hour:02d}:{end_min:02d}")
    else:
        print("No solution found")

solve_scheduling()