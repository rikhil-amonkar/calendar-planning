import z3

def schedule_meeting():
    solver = z3.Solver()
    Day = z3.Int('Day')    # 0: Monday, 1: Tuesday, 2: Wednesday
    S = z3.Int('S')        # Start time in minutes since midnight

    # Work hours constraint: 9:00 (540) to 17:00 (1020)
    solver.add(S >= 540)
    solver.add(S + 30 <= 1020)

    # Blocked intervals for Nancy and Jose per day
    nancy_blocked = {
        0: [(600, 630), (690, 750), (810, 840), (870, 930), (960, 1020)],  # Monday
        1: [(570, 630), (660, 690), (720, 750), (780, 810), (930, 960)],   # Tuesday
        2: [(600, 690), (810, 960)]                                              # Wednesday
    }

    jose_blocked = {
        0: [(540, 1020)],         # Monday
        1: [(540, 1020)],         # Tuesday
        2: [(540, 570), (600, 750), (810, 870), (900, 1020)]  # Wednesday
    }

    # Add constraints for Nancy's blocked times
    for day in nancy_blocked:
        for start_block, end_block in nancy_blocked[day]:
            solver.add(z3.Implies(Day == day, z3.Or(S >= end_block, S + 30 <= start_block)))

    # Add constraints for Jose's blocked times
    for day in jose_blocked:
        for start_block, end_block in jose_blocked[day]:
            solver.add(z3.Implies(Day == day, z3.Or(S >= end_block, S + 30 <= start_block)))

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