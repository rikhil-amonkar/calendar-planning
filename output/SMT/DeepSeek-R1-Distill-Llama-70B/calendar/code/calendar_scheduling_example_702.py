import z3

def schedule_meeting():
    solver = z3.Solver()
    Day = z3.Int('Day')    # 0: Monday, 1: Tuesday, 2: Wednesday
    S = z3.Int('S')        # Start time in minutes since midnight

    # Work hours constraint: 9:00 (540) to 17:00 (1020)
    # Meeting must end by 17:00, so latest start time is 990 (16:30)
    solver.add(S >= 540)    # 9:00 AM
    solver.add(S <= 990)    # 16:30

    # Robert's blocked intervals in minutes since midnight
    robert_blocked = {
        0: [(660, 690), (840, 870), (930, 960)],  # Monday
        1: [(630, 660), (900, 930)],              # Tuesday
        2: [(600, 660), (690, 720), (750, 780), (810, 840), (900, 930), (960, 990)]  # Wednesday
    }

    # Ralph's blocked intervals in minutes since midnight
    ralph_blocked = {
        0: [(600, 810), (840, 870), (900, 1020)],  # Monday
        1: [(540, 570), (600, 630), (660, 690), (720, 780), (840, 930), (960, 1020)],  # Tuesday
        2: [(630, 660), (690, 720), (780, 870), (990, 1020)]  # Wednesday
    }

    # Add constraints for Robert's blocked times
    for day in robert_blocked:
        for start_block, end_block in robert_blocked[day]:
            solver.add(z3.Implies(Day == day, z3.Or(S >= end_block, S + 30 <= start_block)))

    # Add constraints for Ralph's blocked times
    for day in ralph_blocked:
        for start_block, end_block in ralph_blocked[day]:
            solver.add(z3.Implies(Day == day, z3.Or(S >= end_block, S + 30 <= start_block)))

    # Robert's preference: Do not meet on Monday
    solver.add(Day != 0)

    # Minimize the start time to find the earliest availability
    solver.minimize(S)

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