from z3 import *

def solve_meeting_scheduling():
    # Create solver instance
    s = Solver()

    # Define variables
    day = Int('day')
    start_time = Int('start_time')  # in minutes from 00:00

    # Possible days: Monday (0), Tuesday (1), Wednesday (2), Thursday (3)
    s.add(day >= 0, day <= 3)

    # Meeting duration is 30 minutes
    end_time = start_time + 30

    # Work hours are 9:00 to 17:00 (540 to 1020 minutes)
    s.add(start_time >= 540, end_time <= 1020)

    # Betty cannot meet on Monday (day 0)
    s.add(day != 0)

    # Betty cannot meet on Tuesday (day 1) or Thursday (day 3) before 15:00 (900 minutes)
    s.add(Or(
        day != 1,
        start_time >= 900
    ))
    s.add(Or(
        day != 3,
        start_time >= 900
    ))

    # Scott prefers to avoid Wednesday (day 2), but it's not a hard constraint
    # So we first try without Wednesday, and if unsat, we allow Wednesday
    # To model this, we'll use a soft constraint approach
    # But for simplicity, we'll first try without Wednesday, then if unsat, allow it.

    # Function to add busy times for a person on a specific day
    def add_busy_constraints(day_var, start, end, busy_schedule):
        for busy_day, busy_start, busy_end in busy_schedule:
            s.add(Or(
                day_var != busy_day,
                end <= busy_start * 60,  # busy_start is in HH:MM converted to minutes
                start >= busy_end * 60
            ))

    # Betty's busy times (converted to minutes from 00:00)
    betty_busy = [
        (0, 10, 10.5), (0, 13.5, 14), (0, 15, 15.5), (0, 16, 16.5),
        (1, 9, 9.5), (1, 11.5, 12), (1, 12.5, 13), (1, 13.5, 14), (1, 16.5, 17),
        (2, 9.5, 10.5), (2, 13, 13.5), (2, 14, 14.5),
        (3, 9.5, 10), (3, 11.5, 12), (3, 14, 14.5), (3, 15, 15.5), (3, 16.5, 17)
    ]
    # Scott's busy times
    scott_busy = [
        (0, 9.5, 15), (0, 15.5, 16), (0, 16.5, 17),
        (1, 9, 9.5), (1, 10, 11), (1, 11.5, 12), (1, 12.5, 13.5), (1, 14, 15), (1, 16, 16.5),
        (2, 9.5, 12.5), (2, 13, 13.5), (2, 14, 14.5), (2, 15, 15.5), (2, 16, 16.5),
        (3, 9, 9.5), (3, 10, 10.5), (3, 11, 12), (3, 12.5, 13), (3, 15, 16), (3, 16.5, 17)
    ]

    # Add busy constraints for Betty and Scott
    for busy_day, busy_start, busy_end in betty_busy:
        s.add(Or(
            day != busy_day,
            end_time <= busy_start * 60,
            start_time >= busy_end * 60
        ))

    for busy_day, busy_start, busy_end in scott_busy:
        s.add(Or(
            day != busy_day,
            end_time <= busy_start * 60,
            start_time >= busy_end * 60
        ))

    # First, try without Wednesday (day 2)
    temp_solver = Solver()
    temp_solver.add(s.assertions())
    temp_solver.add(day != 2)
    res = temp_solver.check()
    if res == sat:
        m = temp_solver.model()
    else:
        # If unsat, allow Wednesday
        res = s.check()
        m = s.model() if res == sat else None

    if res != sat:
        return "No solution found"

    # Extract solution
    day_val = m[day].as_long()
    start_val = m[start_time].as_long()

    # Convert day_val to day name
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    day_name = days[day_val]

    # Convert start_val to HH:MM
    hours = start_val // 60
    minutes = start_val % 60
    start_time_str = f"{hours:02d}:{minutes:02d}"

    end_val = start_val + 30
    end_hours = end_val // 60
    end_minutes = end_val % 60
    end_time_str = f"{end_hours:02d}:{end_minutes:02d}"

    return f"SOLUTION:\nDay: {day_name}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}"

print(solve_meeting_scheduling())