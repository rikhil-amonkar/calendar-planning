from z3 import *

def solve_scheduling():
    # Define the work hours in minutes from 9:00 (0) to 17:00 (480)
    work_start = 0  # 9:00 in minutes from 9:00
    work_end = 480   # 17:00 in minutes from 9:00
    meeting_duration = 60  # 1 hour in minutes

    # Define the busy intervals for each participant in minutes from 9:00
    kayla_busy = [
        (60, 90),    # 10:00-10:30
        (330, 420)   # 14:30-16:00
    ]
    rebecca_busy = [
        (0, 240),     # 9:00-13:00
        (270, 360),   # 13:30-15:00
        (390, 420)    # 15:30-16:00
    ]

    # Create a Z3 solver instance
    solver = Solver()

    # The meeting start time (in minutes from 9:00)
    start = Int('start')

    # Constraints: start must be within work hours and allow for the meeting duration
    solver.add(start >= work_start)
    solver.add(start + meeting_duration <= work_end)

    # The meeting must not overlap with any of Kayla's busy intervals
    for (busy_start, busy_end) in kayla_busy:
        solver.add(Or(start >= busy_end, start + meeting_duration <= busy_start))

    # The meeting must not overlap with any of Rebecca's busy intervals
    for (busy_start, busy_end) in rebecca_busy:
        solver.add(Or(start >= busy_end, start + meeting_duration <= busy_start))

    # Check if there's a solution
    if solver.check() == sat:
        model = solver.model()
        start_minutes = model[start].as_long()

        # Convert start_minutes back to HH:MM format
        start_hour = 9 + start_minutes // 60
        start_minute = start_minutes % 60
        end_minutes = start_minutes + meeting_duration
        end_hour = 9 + end_minutes // 60
        end_minute = end_minutes % 60

        # Format the output
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_hour:02d}:{start_minute:02d}")
        print(f"End Time: {end_hour:02d}:{end_minute:02d}")
    else:
        print("No solution found")

solve_scheduling()