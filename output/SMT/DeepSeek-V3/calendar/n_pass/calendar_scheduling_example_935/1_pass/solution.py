from z3 import *

def solve_scheduling():
    # Create solver instance
    s = Solver()

    # Define variables
    day = Int('day')  # 0: Monday, 1: Tuesday, ..., 4: Friday
    start_time = Int('start_time')  # in minutes from 9:00 (e.g., 0 is 9:00, 30 is 9:30, etc.)

    # Meeting duration is 30 minutes
    meeting_duration = 30
    end_time = start_time + meeting_duration

    # Work hours: 9:00 to 17:00 (480 minutes from 9:00)
    s.add(day >= 0, day <= 4)
    s.add(start_time >= 0, end_time <= 480)

    # Terry's busy times per day (each entry is (day, start, end) in minutes from 9:00)
    terry_busy = [
        # Monday
        (0, 10*60 + 30 - 9*60, 11*60 - 9*60),
        (0, 12*60 + 30 - 9*60, 14*60 - 9*60),
        (0, 15*60 - 9*60, 17*60 - 9*60),
        # Tuesday
        (1, 9*60 + 30 - 9*60, 10*60 - 9*60),
        (1, 10*60 + 30 - 9*60, 11*60 - 9*60),
        (1, 14*60 - 9*60, 14*60 + 30 - 9*60),
        (1, 16*60 - 9*60, 16*60 + 30 - 9*60),
        # Wednesday
        (2, 9*60 + 30 - 9*60, 10*60 + 30 - 9*60),
        (2, 11*60 - 9*60, 12*60 - 9*60),
        (2, 13*60 - 9*60, 13*60 + 30 - 9*60),
        (2, 15*60 - 9*60, 16*60 - 9*60),
        (2, 16*60 + 30 - 9*60, 17*60 - 9*60),
        # Thursday
        (3, 9*60 + 30 - 9*60, 10*60 - 9*60),
        (3, 12*60 - 9*60, 12*60 + 30 - 9*60),
        (3, 13*60 - 9*60, 14*60 + 30 - 9*60),
        (3, 16*60 - 9*60, 16*60 + 30 - 9*60),
        # Friday
        (4, 9*60 - 9*60, 11*60 + 30 - 9*60),
        (4, 12*60 - 9*60, 12*60 + 30 - 9*60),
        (4, 13*60 + 30 - 9*60, 16*60 - 9*60),
        (4, 16*60 + 30 - 9*60, 17*60 - 9*60),
    ]

    # Frances's busy times per day
    frances_busy = [
        # Monday
        (0, 9*60 + 30 - 9*60, 11*60 - 9*60),
        (0, 11*60 + 30 - 9*60, 13*60 - 9*60),
        (0, 14*60 - 9*60, 14*60 + 30 - 9*60),
        (0, 15*60 - 9*60, 16*60 - 9*60),
        # Tuesday
        (1, 9*60 - 9*60, 9*60 + 30 - 9*60),
        (1, 10*60 - 9*60, 10*60 + 30 - 9*60),
        (1, 11*60 - 9*60, 12*60 - 9*60),
        (1, 13*60 - 9*60, 14*60 + 30 - 9*60),
        (1, 15*60 + 30 - 9*60, 16*60 + 30 - 9*60),
        # Wednesday
        (2, 9*60 + 30 - 9*60, 10*60 - 9*60),
        (2, 10*60 + 30 - 9*60, 11*60 - 9*60),
        (2, 11*60 + 30 - 9*60, 16*60 - 9*60),
        (2, 16*60 + 30 - 9*60, 17*60 - 9*60),
        # Thursday
        (3, 11*60 - 9*60, 12*60 + 30 - 9*60),
        (3, 14*60 + 30 - 9*60, 17*60 - 9*60),
        # Friday
        (4, 9*60 + 30 - 9*60, 10*60 + 30 - 9*60),
        (4, 11*60 - 9*60, 12*60 + 30 - 9*60),
        (4, 13*60 - 9*60, 16*60 - 9*60),
        (4, 16*60 + 30 - 9*60, 17*60 - 9*60),
    ]

    # Add constraints for Terry's busy times
    for d, s_busy, e_busy in terry_busy:
        s.add(Not(And(day == d, start_time < e_busy, end_time > s_busy)))

    # Add constraints for Frances's busy times
    for d, s_busy, e_busy in frances_busy:
        s.add(Not(And(day == d, start_time < e_busy, end_time > s_busy)))

    # Frances prefers to avoid Tuesday, so we try other days first
    # To find the earliest possible time, we can optimize by checking days in order
    # But since Z3 doesn't optimize, we can add a constraint to prefer earlier days
    # Alternatively, we can iterate days in order and check for a solution

    # Check for solutions in day order: Monday to Friday, preferring earlier days
    solution_found = False
    solution_day = None
    solution_start = None

    days_order = [0, 2, 3, 4, 1]  # Tuesday (1) is last
    day_names = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]

    for d in days_order:
        temp_solver = Solver()
        temp_solver.add(s.assertions())
        temp_solver.add(day == d)
        if temp_solver.check() == sat:
            model = temp_solver.model()
            solution_day = model[day].as_long()
            solution_start = model[start_time].as_long()
            solution_found = True
            break

    if not solution_found:
        print("No solution found")
        return

    # Convert solution to readable format
    day_name = day_names[solution_day]
    start_hour = 9 + solution_start // 60
    start_min = solution_start % 60
    end_time_val = solution_start + 30
    end_hour = 9 + end_time_val // 60
    end_min = end_time_val % 60

    print(f"SOLUTION:")
    print(f"Day: {day_name}")
    print(f"Start Time: {start_hour:02d}:{start_min:02d}")
    print(f"End Time: {end_hour:02d}:{end_min:02d}")

solve_scheduling()