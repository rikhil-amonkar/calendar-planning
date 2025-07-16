from z3 import *

def schedule_meeting():
    # Define the variables
    start_time = Int('start_time')  # in minutes from 9:00 (540 minutes in 24-hour format)

    # Initialize the solver
    s = Solver()

    # Work hours: 9:00 to 17:00 (540 to 1020 minutes in 24-hour format)
    work_start = 540  # 9:00 in minutes (9 * 60)
    work_end = 1020    # 17:00 in minutes (17 * 60)

    # Meeting duration is 30 minutes
    duration = 30

    # Constraints for work hours
    s.add(start_time >= work_start)
    s.add(start_time + duration <= work_end)

    # Judy's schedule: free all day, no constraints beyond work hours

    # Nicole's schedule:
    # Meetings: 9:00-10:00 (540-600), 10:30-16:30 (630-990)
    # So Nicole is busy from 540-600 and 630-990
    # So free times for Nicole are 600-630 and 990-1020
    # Also, Nicole prefers not before 16:00 (960 minutes)
    # So possible free slots: 990-1020 (since 600-630 is before 16:00)

    # The meeting must not overlap with Nicole's busy times
    # The meeting is [start_time, start_time + 30]
    # It should not overlap with [540, 600] or [630, 990]
    s.add(Or(
        start_time + duration <= 540,  # meeting ends before 9:00
        start_time >= 600              # meeting starts after 10:00
    ))
    s.add(Or(
        start_time + duration <= 630,  # meeting ends before 10:30
        start_time >= 990              # meeting starts after 16:30
    ))

    # Nicole's preference: not before 16:00 (960 minutes)
    # So start_time should be >= 960
    s.add(start_time >= 960)

    # Check if there's a solution
    if s.check() == sat:
        m = s.model()
        start_min = m[start_time].as_long()
        start_hour = start_min // 60
        start_minute = start_min % 60
        end_min = start_min + duration
        end_hour = end_min // 60
        end_minute = end_min % 60

        # Format the output
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_hour:02d}:{start_minute:02d}")
        print(f"End Time: {end_hour:02d}:{end_minute:02d}")
    else:
        print("No solution found")

schedule_meeting()