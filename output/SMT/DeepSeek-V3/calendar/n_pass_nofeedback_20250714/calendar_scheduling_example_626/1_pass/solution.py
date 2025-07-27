from z3 import *

def solve_scheduling():
    # Create the solver
    s = Solver()

    # Define the possible days: Monday (0) or Tuesday (1)
    day = Int('day')
    s.add(Or(day == 0, day == 1))

    # Define the start time in minutes from 9:00 (540 minutes) to 16:00 (960 minutes) since meeting is 1 hour
    start_time = Int('start_time')
    s.add(start_time >= 540)  # 9:00 in minutes (9*60)
    s.add(start_time <= 960)  # 16:00 in minutes (16*60), since end time is start_time + 60 <= 1020 (17:00)

    # Patricia's busy times for Monday and Tuesday
    patricia_monday_busy = [
        (600, 630),    # 10:00-10:30
        (690, 720),     # 11:30-12:00
        (780, 810),     # 13:00-13:30
        (870, 930),     # 14:30-15:30
        (960, 990),     # 16:00-16:30
    ]
    patricia_tuesday_busy = [
        (600, 630),     # 10:00-10:30
        (660, 720),     # 11:00-12:00
        (840, 960),     # 14:00-16:00
        (990, 1020),    # 16:30-17:00
    ]

    # Jesse's busy times for Monday and Tuesday
    jesse_monday_busy = [
        (540, 1020),    # 9:00-17:00 (whole day blocked)
    ]
    jesse_tuesday_busy = [
        (660, 690),     # 11:00-11:30
        (720, 750),     # 12:00-12:30
        (780, 840),     # 13:00-14:00
        (870, 900),     # 14:30-15:00
        (930, 1020),    # 15:30-17:00
    ]

    # Function to check if the selected time overlaps with any busy times
    def no_overlap(day_val, start, end, busy_times):
        constraints = []
        for busy_start, busy_end in busy_times:
            constraints.append(Or(
                end <= busy_start,
                start >= busy_end
            ))
        return And(*constraints)

    # Constraints for Patricia and Jesse based on the selected day
    patricia_constraint = If(day == 0,
        no_overlap(0, start_time, start_time + 60, patricia_monday_busy),
        no_overlap(1, start_time, start_time + 60, patricia_tuesday_busy)
    )
    jesse_constraint = If(day == 0,
        no_overlap(0, start_time, start_time + 60, jesse_monday_busy),
        no_overlap(1, start_time, start_time + 60, jesse_tuesday_busy)
    )

    s.add(patricia_constraint)
    s.add(jesse_constraint)

    # Check for a solution
    if s.check() == sat:
        model = s.model()
        day_val = model[day].as_long()
        start_val = model[start_time].as_long()

        # Determine the day
        day_str = "Monday" if day_val == 0 else "Tuesday"

        # Convert start time from minutes to HH:MM format
        hours = start_val // 60
        minutes = start_val % 60
        start_time_str = f"{hours:02d}:{minutes:02d}"

        # Calculate end time (start + 60 minutes)
        end_time_val = start_val + 60
        end_hours = end_time_val // 60
        end_minutes = end_time_val % 60
        end_time_str = f"{end_hours:02d}:{end_minutes:02d}"

        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_scheduling()