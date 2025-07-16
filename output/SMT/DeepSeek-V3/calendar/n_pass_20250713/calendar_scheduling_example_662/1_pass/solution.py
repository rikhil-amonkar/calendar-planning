from z3 import *

def solve_meeting_scheduling():
    # Create solver instance
    s = Solver()

    # Define possible days (0 for Monday, 1 for Tuesday)
    day = Int('day')
    s.add(Or(day == 0, day == 1))

    # Define start time in minutes from 9:00 (540 minutes) to 17:00 (1020 minutes)
    start_time = Int('start_time')
    s.add(start_time >= 540)  # 9:00 in minutes
    s.add(start_time + 60 <= 1020)  # Meeting ends by 17:00 (60 minutes duration)

    # Gary's blocked times
    gary_monday_blocked = [
        (570, 600),   # 9:30-10:00
        (660, 780),    # 11:00-13:00
        (840, 870),     # 14:00-14:30
        (990, 1020)     # 16:30-17:00
    ]
    gary_tuesday_blocked = [
        (540, 570),     # 9:00-9:30
        (630, 660),     # 10:30-11:00
        (870, 960)      # 14:30-16:00
    ]

    # David's blocked times
    david_monday_blocked = [
        (540, 570),     # 9:00-9:30
        (600, 780),     # 10:00-13:00
        (870, 990)      # 14:30-16:30
    ]
    david_tuesday_blocked = [
        (540, 570),     # 9:00-9:30
        (600, 630),     # 10:00-10:30
        (660, 750),     # 11:00-12:30
        (780, 870),     # 13:00-14:30
        (900, 960),     # 15:00-16:00
        (990, 1020)     # 16:30-17:00
    ]

    # Function to add constraints for not overlapping with blocked times
    def add_no_overlap_constraints(day_var, start, duration, blocked_times_day0, blocked_times_day1):
        constraints = []
        # For each blocked time in day 0 (Monday)
        for (block_start, block_end) in blocked_times_day0:
            constraints.append(Or(
                day_var != 0,
                start >= block_end,
                start + duration <= block_start
            ))
        # For each blocked time in day 1 (Tuesday)
        for (block_start, block_end) in blocked_times_day1:
            constraints.append(Or(
                day_var != 1,
                start >= block_end,
                start + duration <= block_start
            ))
        return constraints

    # Add constraints for Gary
    gary_constraints = add_no_overlap_constraints(day, start_time, 60, gary_monday_blocked, gary_tuesday_blocked)
    for c in gary_constraints:
        s.add(c)

    # Add constraints for David
    david_constraints = add_no_overlap_constraints(day, start_time, 60, david_monday_blocked, david_tuesday_blocked)
    for c in david_constraints:
        s.add(c)

    # Check for a solution
    if s.check() == sat:
        m = s.model()
        day_val = m[day].as_long()
        start_val = m[start_time].as_long()

        # Determine day name
        day_name = "Monday" if day_val == 0 else "Tuesday"

        # Convert start time from minutes to HH:MM
        start_hh = start_val // 60
        start_mm = start_val % 60
        start_time_str = f"{start_hh:02d}:{start_mm:02d}"

        # Calculate end time
        end_val = start_val + 60
        end_hh = end_val // 60
        end_mm = end_val % 60
        end_time_str = f"{end_hh:02d}:{end_mm:02d}"

        # Output the solution
        print("SOLUTION:")
        print(f"Day: {day_name}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_meeting_scheduling()