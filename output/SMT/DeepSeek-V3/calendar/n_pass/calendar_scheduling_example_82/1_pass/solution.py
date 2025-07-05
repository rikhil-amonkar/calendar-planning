from z3 import *

def find_meeting_time():
    # Initialize the solver
    s = Solver()

    # Define the work hours (9:00 to 17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes

    # Meeting duration is 30 minutes
    meeting_duration = 30

    # Define the start time of the meeting as a Z3 variable
    start_time = Int('start_time')
    end_time = start_time + meeting_duration

    # Constraint: meeting must be within work hours
    s.add(start_time >= work_start)
    s.add(end_time <= work_end)

    # Michael's busy times (in minutes since 9:00)
    michael_busy = [
        (9 * 60 + 30, 10 * 60 + 30),  # 9:30-10:30
        (15 * 60, 15 * 60 + 30),       # 15:00-15:30
        (16 * 60, 16 * 60 + 30)        # 16:00-16:30
    ]

    # Arthur's busy times (in minutes since 9:00)
    arthur_busy = [
        (9 * 60, 12 * 60),            # 9:00-12:00
        (13 * 60, 15 * 60),            # 13:00-15:00
        (15 * 60 + 30, 16 * 60),       # 15:30-16:00
        (16 * 60 + 30, 17 * 60)        # 16:30-17:00
    ]

    # Eric is free all day, so no constraints for him

    # Add constraints for Michael: meeting must not overlap with his busy times
    for busy_start, busy_end in michael_busy:
        s.add(Or(
            end_time <= busy_start,
            start_time >= busy_end
        ))

    # Add constraints for Arthur: meeting must not overlap with his busy times
    for busy_start, busy_end in arthur_busy:
        s.add(Or(
            end_time <= busy_start,
            start_time >= busy_end
        ))

    # Check if there's a solution
    if s.check() == sat:
        m = s.model()
        start = m[start_time].as_long()
        # Convert start time from minutes to HH:MM format
        hours = start // 60
        minutes = start % 60
        start_str = f"{hours:02d}:{minutes:02d}"
        # Calculate end time
        end = start + meeting_duration
        hours_end = end // 60
        minutes_end = end % 60
        end_str = f"{hours_end:02d}:{minutes_end:02d}"
        # Print the solution
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_str}")
        print(f"End Time: {end_str}")
    else:
        print("No solution found")

find_meeting_time()