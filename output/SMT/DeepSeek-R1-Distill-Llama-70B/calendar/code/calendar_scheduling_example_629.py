import z3

def schedule_meeting():
    solver = z3.Solver()
    Day = z3.Int('Day')    # 0: Monday, 1: Tuesday
    S = z3.Int('S')        # Start time in minutes since midnight

    # Work hours constraint: 9:00 (540) to 17:00 (1020)
    solver.add(S >= 540)
    solver.add(S + 30 <= 1020)

    # Margaret's blocked intervals
    margaret_blocked = {
        0: [(630, 660), (690, 720), (780, 810), (900, 1020)],  # Monday
        1: [(720, 750)]                                             # Tuesday
    }

    # Alexis's blocked intervals
    alexis_blocked = {
        0: [(570, 690), (750, 780), (840, 1020)],  # Monday
        1: [(540, 570), (600, 630), (840, 990)]     # Tuesday
    }

    # Add constraints for Margaret's blocked times
    for day in margaret_blocked:
        for start_block, end_block in margaret_blocked[day]:
            solver.add(z3.Implies(Day == day, z3.Or(S >= end_block, S + 30 <= start_block)))

    # Add constraints for Alexis's blocked times
    for day in alexis_blocked:
        for start_block, end_block in alexis_blocked[day]:
            solver.add(z3.Implies(Day == day, z3.Or(S >= end_block, S + 30 <= start_block)))

    # Margaret's preferences: Do not meet on Monday and prefer Tuesday before 14:30
    solver.add(Day == 1)  # Only consider Tuesday
    solver.add(S <= 870)  # 14:30 or earlier

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

        day_str = ["Monday", "Tuesday"][day]
        print(f"Day: {day_str}")
        print(f"Start time: {to_time(start)}")
        print(f"End time: {to_time(end)}")
    else:
        print("No solution found.")

schedule_meeting()