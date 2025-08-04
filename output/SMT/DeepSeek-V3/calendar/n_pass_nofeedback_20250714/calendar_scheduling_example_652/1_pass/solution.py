from z3 import *

def solve_scheduling_problem():
    # Create the solver
    solver = Solver()

    # Define the variables
    day = Int('day')  # 0 for Monday, 1 for Tuesday
    start_time = Int('start_time')  # in minutes since midnight
    end_time = Int('end_time')

    # Constraints for day
    solver.add(Or(day == 0, day == 1))

    # Meeting duration is 30 minutes
    solver.add(end_time == start_time + 30)

    # Work hours are 9:00 to 17:00 (540 to 1020 minutes)
    solver.add(start_time >= 9 * 60)
    solver.add(end_time <= 17 * 60)

    # Jesse's busy times
    # Monday: 13:30-14:00 (810-840), 14:30-15:00 (870-900)
    # Tuesday: 9:00-9:30 (540-570), 13:00-13:30 (780-810), 14:00-15:00 (840-900)
    # Lawrence's busy times
    # Monday: 9:00-17:00 (540-1020) -> entire day busy
    # Tuesday: 9:30-10:30 (570-630), 11:30-12:30 (690-750), 13:00-13:30 (780-810), 14:30-15:00 (870-900), 15:30-16:30 (930-990)
    # Lawrence cannot meet on Tuesday after 16:30 (i.e., meeting must end by 16:30)

    # Constraints for Jesse and Lawrence's schedules
    # For Jesse: the meeting should not overlap with any of Jesse's meetings on the selected day
    jesse_monday_busy = Or(
        And(day == 0, Or(
            And(start_time < 810, end_time > 540),  # overlaps with 13:30-14:00 (810-840)
            And(start_time < 840, end_time > 810),
            And(start_time < 870, end_time > 840),  # overlaps with 14:30-15:00 (870-900)
            And(start_time < 900, end_time > 870)
        )),
        And(day == 1, Or(
            And(start_time < 570, end_time > 540),  # overlaps with 9:00-9:30 (540-570)
            And(start_time < 570, end_time > 540),
            And(start_time < 810, end_time > 780),  # overlaps with 13:00-13:30 (780-810)
            And(start_time < 810, end_time > 780),
            And(start_time < 900, end_time > 840)   # overlaps with 14:00-15:00 (840-900)
        ))
    )
    solver.add(Not(jesse_monday_busy))

    # For Lawrence: the meeting should not overlap with any of Lawrence's meetings on the selected day
    # Lawrence is busy all day Monday (540-1020), so day can't be 0
    solver.add(day != 0)

    # For Tuesday:
    lawrence_tuesday_busy = Or(
        And(start_time < 630, end_time > 570),  # 9:30-10:30 (570-630)
        And(start_time < 750, end_time > 690),   # 11:30-12:30 (690-750)
        And(start_time < 810, end_time > 780),   # 13:00-13:30 (780-810)
        And(start_time < 900, end_time > 870),   # 14:30-15:00 (870-900)
        And(start_time < 990, end_time > 930)    # 15:30-16:30 (930-990)
    )
    solver.add(Not(lawrence_tuesday_busy))

    # Additional constraint: Lawrence cannot meet on Tuesday after 16:30 (so end_time <= 990)
    solver.add(end_time <= 16 * 60 + 30)

    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        day_val = model[day].as_long()
        start_val = model[start_time].as_long()
        end_val = model[end_time].as_long()

        day_str = "Monday" if day_val == 0 else "Tuesday"
        start_hh = start_val // 60
        start_mm = start_val % 60
        end_hh = end_val // 60
        end_mm = end_val % 60

        # Formatting to HH:MM with leading zeros
        start_time_str = f"{start_hh:02d}:{start_mm:02d}"
        end_time_str = f"{end_hh:02d}:{end_mm:02d}"

        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_scheduling_problem()