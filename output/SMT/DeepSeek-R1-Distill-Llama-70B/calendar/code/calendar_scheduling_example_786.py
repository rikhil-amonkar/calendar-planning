import z3

def schedule_meeting():
    solver = z3.Solver()
    Day = z3.Int('Day')    # 0: Monday, 1: Tuesday, 2: Wednesday
    S = z3.Int('S')        # Start time in minutes since midnight

    # Work hours constraint: 9:00 (540) to 17:00 (1020)
    solver.add(S >= 540)
    solver.add(S + 30 <= 1020)

    # Amy's blocked intervals
    amy_blocked = {
        2: [(660, 690), (810, 840)]  # Wednesday: 11:00-11:30, 13:30-14:00
    }

    # Pamela's blocked intervals
    pamela_blocked = {
        0: [(540, 630), (660, 990)],           # Monday: 9:00-10:30, 11:00-16:30
        1: [(540, 570), (600, 1020)],         # Tuesday: 9:00-9:30, 10:00-17:00
        2: [(540, 570), (600, 660), (690, 810), (870, 900), (960, 990)]  # Wednesday: 9:00-9:30, 10:00-11:00, 11:30-13:30, 14:30-15:00, 16:00-16:30
    }

    # Add constraints for Amy's blocked times
    for day in amy_blocked:
        for start_block, end_block in amy_blocked[day]:
            solver.add(z3.Implies(Day == day, z3.Or(S >= end_block, S + 30 <= start_block)))

    # Add constraints for Pamela's blocked times
    for day in pamela_blocked:
        for start_block, end_block in pamela_blocked[day]:
            solver.add(z3.Implies(Day == day, z3.Or(S >= end_block, S + 30 <= start_block)))

    # Preference: Avoid Monday and Tuesday, prefer Wednesday before 16:00
    solver.add(Day == 2)  # Only consider Wednesday
    solver.add(S <= 960)  # Latest start time is 16:00 (960 minutes)

    # Solve the constraints
    if solver.check() == z3.sat:
        model = solver.model()
        day = model[Day].as_long()
        start = model[S].as_long()
        end = start + 30

        # Convert minutes to HH:MM format
        def to_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"

        day_str = ["Monday", "Tuesday", "Wednesday"][day]
        print(f"Day: {day_str}")
        print(f"Start time: {to_time(start)}")
        print(f"End time: {to_time(end)}")
    else:
        print("No solution found.")

schedule_meeting()