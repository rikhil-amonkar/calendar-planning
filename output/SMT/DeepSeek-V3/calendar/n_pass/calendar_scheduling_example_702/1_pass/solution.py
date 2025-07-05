from z3 import *

def solve_scheduling():
    # Create solver instance
    s = Solver()

    # Define possible days (0: Monday, 1: Tuesday, 2: Wednesday)
    day = Int('day')
    s.add(day >= 0, day <= 2)

    # Define start and end times in minutes since 9:00 (540 minutes)
    start_time = Int('start_time')
    end_time = Int('end_time')
    s.add(start_time >= 540, end_time <= 1020)  # 9:00 to 17:00 in minutes
    s.add(end_time == start_time + 30)  # Meeting duration is 30 minutes

    # Robert's schedule: day, start, end (in minutes since 9:00)
    robert_busy = [
        (0, 660, 690),   # Mon 11:00-11:30
        (0, 840, 870),    # Mon 14:00-14:30
        (0, 930, 960),    # Mon 15:30-16:00
        (1, 750, 780),    # Tue 10:30-11:00
        (1, 900, 930),    # Tue 15:00-15:30
        (2, 600, 660),    # Wed 10:00-11:00
        (2, 690, 720),    # Wed 11:30-12:00
        (2, 750, 780),    # Wed 12:30-13:00
        (2, 810, 840),    # Wed 13:30-14:00
        (2, 900, 930),    # Wed 15:00-15:30
        (2, 960, 990)     # Wed 16:00-16:30
    ]

    # Ralph's schedule: day, start, end (in minutes since 9:00)
    ralph_busy = [
        (0, 600, 870),    # Mon 10:00-13:30
        (0, 840, 870),    # Mon 14:00-14:30
        (0, 900, 1020),   # Mon 15:00-17:00
        (1, 540, 570),    # Tue 9:00-9:30
        (1, 600, 630),    # Tue 10:00-10:30
        (1, 660, 690),    # Tue 11:00-11:30
        (1, 720, 780),    # Tue 12:00-13:00
        (1, 840, 930),    # Tue 14:00-15:30
        (1, 960, 1020),   # Tue 16:00-17:00
        (2, 630, 660),    # Wed 10:30-11:00
        (2, 690, 720),    # Wed 11:30-12:00
        (2, 780, 870),    # Wed 13:00-14:30
        (2, 990, 1020)    # Wed 16:30-17:00
    ]

    # Constraint: meeting does not overlap with Robert's busy times
    for (d, busy_start, busy_end) in robert_busy:
        s.add(Not(And(day == d, start_time < busy_end, end_time > busy_start)))

    # Constraint: meeting does not overlap with Ralph's busy times
    for (d, busy_start, busy_end) in ralph_busy:
        s.add(Not(And(day == d, start_time < busy_end, end_time > busy_start)))

    # Robert prefers to avoid more meetings on Monday (day 0)
    # We add a soft constraint to prioritize other days
    # To find the earliest time, we minimize (day * 1440 + start_time)
    # This ensures earliest day and earliest time on that day
    objective = day * 1440 + start_time
    opt = Optimize()
    opt.add(s.assertions())
    opt.minimize(objective)

    # Check for a solution
    if opt.check() == sat:
        m = opt.model()
        day_val = m[day].as_long()
        start_val = m[start_time].as_long()
        end_val = m[end_time].as_long()

        # Convert day number to day name
        days = ["Monday", "Tuesday", "Wednesday"]
        day_name = days[day_val]

        # Convert minutes to HH:MM format
        start_hh = start_val // 60
        start_mm = start_val % 60
        end_hh = end_val // 60
        end_mm = end_val % 60

        # Format the solution
        solution = f"SOLUTION:\nDay: {day_name}\nStart Time: {start_hh:02d}:{start_mm:02d}\nEnd Time: {end_hh:02d}:{end_mm:02d}"
        return solution
    else:
        return "No solution found."

# Print the solution
print(solve_scheduling())