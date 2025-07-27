from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define the possible days (0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday)
    day = Int('day')
    s.add(day >= 0, day <= 3)

    # Define the start time in minutes from 9:00 (540 minutes in 24-hour format)
    start_time = Int('start_time')
    s.add(start_time >= 0, start_time <= 8 * 60)  # 9:00-17:00 is 8 hours (480 minutes)

    # Meeting duration is 30 minutes
    duration = 30
    end_time = start_time + duration
    s.add(end_time <= 8 * 60)

    # Betty's constraints
    # Betty cannot meet on Monday (day 0)
    s.add(day != 0)
    # Betty cannot meet before 15:00 on Tuesday (day 1) and Thursday (day 3)
    s.add(Or(day != 1, start_time >= (15 - 9) * 60))
    s.add(Or(day != 3, start_time >= (15 - 9) * 60))

    # Scott prefers to avoid Wednesday (day 2), but it's not a hard constraint
    # So we first try without Wednesday, if no solution, then allow Wednesday
    # We'll handle this by checking two scenarios

    # Function to add busy time constraints
    def add_busy_constraints(day_var, start, end, busy_day, busy_start, busy_end):
        # Convert busy times to minutes since 9:00
        busy_start_min = (busy_start[0] - 9) * 60 + busy_start[1]
        busy_end_min = (busy_end[0] - 9) * 60 + busy_end[1]
        # The meeting does not overlap with the busy slot
        s.add(Or(
            day_var != busy_day,
            end <= busy_start_min,
            start >= busy_end_min
        ))

    # Betty's busy times
    # Monday (day 0): 10:00-10:30, 13:30-14:00, 15:00-15:30, 16:00-16:30
    add_busy_constraints(day, start_time, end_time, 0, (10, 0), (10, 30))
    add_busy_constraints(day, start_time, end_time, 0, (13, 30), (14, 0))
    add_busy_constraints(day, start_time, end_time, 0, (15, 0), (15, 30))
    add_busy_constraints(day, start_time, end_time, 0, (16, 0), (16, 30))
    # Tuesday (day 1): 9:00-9:30, 11:30-12:00, 12:30-13:00, 13:30-14:00, 16:30-17:00
    add_busy_constraints(day, start_time, end_time, 1, (9, 0), (9, 30))
    add_busy_constraints(day, start_time, end_time, 1, (11, 30), (12, 0))
    add_busy_constraints(day, start_time, end_time, 1, (12, 30), (13, 0))
    add_busy_constraints(day, start_time, end_time, 1, (13, 30), (14, 0))
    add_busy_constraints(day, start_time, end_time, 1, (16, 30), (17, 0))
    # Wednesday (day 2): 9:30-10:30, 13:00-13:30, 14:00-14:30
    add_busy_constraints(day, start_time, end_time, 2, (9, 30), (10, 30))
    add_busy_constraints(day, start_time, end_time, 2, (13, 0), (13, 30))
    add_busy_constraints(day, start_time, end_time, 2, (14, 0), (14, 30))
    # Thursday (day 3): 9:30-10:00, 11:30-12:00, 14:00-14:30, 15:00-15:30, 16:30-17:00
    add_busy_constraints(day, start_time, end_time, 3, (9, 30), (10, 0))
    add_busy_constraints(day, start_time, end_time, 3, (11, 30), (12, 0))
    add_busy_constraints(day, start_time, end_time, 3, (14, 0), (14, 30))
    add_busy_constraints(day, start_time, end_time, 3, (15, 0), (15, 30))
    add_busy_constraints(day, start_time, end_time, 3, (16, 30), (17, 0))

    # Scott's busy times
    # Monday (day 0): 9:30-15:00, 15:30-16:00, 16:30-17:00
    add_busy_constraints(day, start_time, end_time, 0, (9, 30), (15, 0))
    add_busy_constraints(day, start_time, end_time, 0, (15, 30), (16, 0))
    add_busy_constraints(day, start_time, end_time, 0, (16, 30), (17, 0))
    # Tuesday (day 1): 9:00-9:30, 10:00-11:00, 11:30-12:00, 12:30-13:30, 14:00-15:00, 16:00-16:30
    add_busy_constraints(day, start_time, end_time, 1, (9, 0), (9, 30))
    add_busy_constraints(day, start_time, end_time, 1, (10, 0), (11, 0))
    add_busy_constraints(day, start_time, end_time, 1, (11, 30), (12, 0))
    add_busy_constraints(day, start_time, end_time, 1, (12, 30), (13, 30))
    add_busy_constraints(day, start_time, end_time, 1, (14, 0), (15, 0))
    add_busy_constraints(day, start_time, end_time, 1, (16, 0), (16, 30))
    # Wednesday (day 2): 9:30-12:30, 13:00-13:30, 14:00-14:30, 15:00-15:30, 16:00-16:30
    add_busy_constraints(day, start_time, end_time, 2, (9, 30), (12, 30))
    add_busy_constraints(day, start_time, end_time, 2, (13, 0), (13, 30))
    add_busy_constraints(day, start_time, end_time, 2, (14, 0), (14, 30))
    add_busy_constraints(day, start_time, end_time, 2, (15, 0), (15, 30))
    add_busy_constraints(day, start_time, end_time, 2, (16, 0), (16, 30))
    # Thursday (day 3): 9:00-9:30, 10:00-10:30, 11:00-12:00, 12:30-13:00, 15:00-16:00, 16:30-17:00
    add_busy_constraints(day, start_time, end_time, 3, (9, 0), (9, 30))
    add_busy_constraints(day, start_time, end_time, 3, (10, 0), (10, 30))
    add_busy_constraints(day, start_time, end_time, 3, (11, 0), (12, 0))
    add_busy_constraints(day, start_time, end_time, 3, (12, 30), (13, 0))
    add_busy_constraints(day, start_time, end_time, 3, (15, 0), (16, 0))
    add_busy_constraints(day, start_time, end_time, 3, (16, 30), (17, 0))

    # First, try without Wednesday (Scott's preference)
    temp_solver = Solver()
    temp_solver.add(s.assertions())
    temp_solver.add(day != 2)  # Avoid Wednesday
    if temp_solver.check() == sat:
        m = temp_solver.model()
    else:
        # If no solution without Wednesday, try including Wednesday
        if s.check() == sat:
            m = s.model()
        else:
            return None

    # Extract the solution
    day_val = m[day].as_long()
    start_val = m[start_time].as_long()

    # Convert day_val to day name
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    day_name = days[day_val]

    # Convert start_val to HH:MM
    start_hour = 9 + start_val // 60
    start_min = start_val % 60
    end_hour = 9 + (start_val + duration) // 60
    end_min = (start_val + duration) % 60

    # Format the output
    return f"SOLUTION:\nDay: {day_name}\nStart Time: {start_hour:02d}:{start_min:02d}\nEnd Time: {end_hour:02d}:{end_min:02d}"

# Execute the solver and print the solution
solution = solve_scheduling()
print(solution)