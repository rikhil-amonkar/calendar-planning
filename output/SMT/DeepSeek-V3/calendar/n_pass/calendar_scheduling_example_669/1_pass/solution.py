from z3 import *

def solve_scheduling():
    # Create solver instance
    s = Solver()

    # Define variables
    day = Int('day')  # 0 for Monday, 1 for Tuesday
    start_time = Int('start_time')  # in minutes from 9:00 (0 to 480 (8 hours))

    # Constants
    meeting_duration = 30
    work_start = 0  # 9:00 in minutes from 9:00
    work_end = 480   # 17:00 is 8*60=480 minutes from 9:00

    # Constraints for day: 0 (Monday) or 1 (Tuesday)
    s.add(Or(day == 0, day == 1))

    # Constraints for start_time: must allow meeting to finish by 17:00
    s.add(start_time >= work_start)
    s.add(start_time + meeting_duration <= work_end)

    # Jean's constraints
    # On Tuesday (day 1), Jean is busy 11:30-12:00 and 16:00-16:30
    # Convert these times to minutes from 9:00:
    # 11:30 is 2.5 hours = 150 minutes
    # 12:00 is 3 hours = 180 minutes
    # 16:00 is 7 hours = 420 minutes
    # 16:30 is 7.5 hours = 450 minutes
    jean_busy1_start = 150
    jean_busy1_end = 180
    jean_busy2_start = 420
    jean_busy2_end = 450

    # The meeting should not overlap with Jean's busy times on Tuesday
    s.add(Implies(day == 1, 
                  And(Not(And(start_time < jean_busy1_end, start_time + meeting_duration > jean_busy1_start)),
                      Not(And(start_time < jean_busy2_end, start_time + meeting_duration > jean_busy2_start)))))

    # Doris's constraints
    # On Monday (day 0), busy times:
    # 9:00-11:30 (0 to 150 minutes)
    # 12:00-12:30 (180 to 210 minutes)
    # 13:30-16:00 (270 to 420 minutes)
    # 16:30-17:00 (450 to 480 minutes)
    doris_monday_busy = [
        (0, 150),
        (180, 210),
        (270, 420),
        (450, 480)
    ]
    # On Tuesday (day 1), busy all day (so meeting can't be on Tuesday)
    s.add(Implies(day == 1, False))  # Because Doris is busy all day Tuesday

    # For Monday, the meeting must not overlap with any of Doris's busy times
    for (busy_start, busy_end) in doris_monday_busy:
        s.add(Implies(day == 0, 
                      Not(And(start_time < busy_end, start_time + meeting_duration > busy_start))))

    # Doris's preference: not after 14:00 on Monday, so meeting must end by 14:00
    # 14:00 is 5 hours from 9:00 = 300 minutes
    s.add(Implies(day == 0, start_time + meeting_duration <= 300))

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        day_val = m[day].as_long()
        start_val = m[start_time].as_long()

        # Convert day_val to day name
        day_name = "Monday" if day_val == 0 else "Tuesday"

        # Calculate start and end times in HH:MM format
        start_hour = 9 + start_val // 60
        start_min = start_val % 60
        end_time_val = start_val + meeting_duration
        end_hour = 9 + end_time_val // 60
        end_min = end_time_val % 60

        # Formatting to two digits
        start_time_str = f"{start_hour:02d}:{start_min:02d}"
        end_time_str = f"{end_hour:02d}:{end_min:02d}"

        print("SOLUTION:")
        print(f"Day: {day_name}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_scheduling()