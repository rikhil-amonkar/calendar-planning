from z3 import *

def solve_meeting_schedule():
    # Create a solver instance
    s = Solver()

    # Define possible days (0: Monday, 1: Tuesday, 2: Wednesday)
    day = Int('day')
    s.add(day >= 0, day <= 2)

    # Define start time in minutes from 9:00 (540 minutes) to 17:00 (1020 minutes)
    start_time = Int('start_time')
    s.add(start_time >= 540, start_time + 60 <= 1020)  # Meeting duration is 60 minutes

    # Define the constraints based on the day and participants' blocked times
    # Martha's blocked times:
    # Monday: 16:00-17:00 (960-1020)
    # Tuesday: 15:00-15:30 (900-930)
    # Wednesday: 10:00-11:00 (600-660), 14:00-14:30 (840-870)
    # Beverly's blocked times:
    # Monday: 9:00-13:30 (540-810), 14:00-17:00 (840-1020)
    # Tuesday: 9:00-17:00 (540-1020)
    # Wednesday: 9:30-15:30 (570-930), 16:30-17:00 (990-1020)

    # Constraints for each day
    # We'll use day to be 0, 1, or 2 and add respective constraints
    # For Monday (day 0)
    monday_constraints = And(
        day == 0,
        # Martha's blocked: 16:00-17:00 (960-1020)
        Not(And(start_time < 960 + 60, start_time + 60 > 960)),
        # Beverly's blocked: 9:00-13:30 (540-810), 14:00-17:00 (840-1020)
        Not(And(start_time < 810, start_time + 60 > 540)),
        Not(And(start_time < 1020, start_time + 60 > 840))
    )

    # For Tuesday (day 1)
    tuesday_constraints = And(
        day == 1,
        # Martha's blocked: 15:00-15:30 (900-930)
        Not(And(start_time < 930, start_time + 60 > 900)),
        # Beverly's blocked: 9:00-17:00 (540-1020)
        Not(And(start_time < 1020, start_time + 60 > 540))
    )

    # For Wednesday (day 2)
    wednesday_constraints = And(
        day == 2,
        # Martha's blocked: 10:00-11:00 (600-660), 14:00-14:30 (840-870)
        Not(And(start_time < 660, start_time + 60 > 600)),
        Not(And(start_time < 870, start_time + 60 > 840)),
        # Beverly's blocked: 9:30-15:30 (570-930), 16:30-17:00 (990-1020)
        Not(And(start_time < 930, start_time + 60 > 570)),
        Not(And(start_time < 1020, start_time + 60 > 990))
    )

    s.add(Or(monday_constraints, tuesday_constraints, wednesday_constraints))

    # Check for a solution
    if s.check() == sat:
        model = s.model()
        day_val = model[day].as_long()
        start_time_val = model[start_time].as_long()

        # Convert start_time_val (minutes from 0:00) to HH:MM
        hours = start_time_val // 60
        minutes = start_time_val % 60
        start_time_str = f"{hours:02d}:{minutes:02d}"

        end_time_val = start_time_val + 60
        end_hours = end_time_val // 60
        end_minutes = end_time_val % 60
        end_time_str = f"{end_hours:02d}:{end_minutes:02d}"

        # Determine the day string
        days = ["Monday", "Tuesday", "Wednesday"]
        day_str = days[day_val]

        # Print the solution in the required format
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_meeting_schedule()