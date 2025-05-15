import z3

def schedule_meeting():
    solver = z3.Solver()
    Day = z3.Int('Day')    # 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday, 4: Friday
    S = z3.Int('S')        # Start time in minutes since midnight

    # Work hours constraint: 9:00 (540) to 17:00 (1020)
    solver.add(S >= 540)
    solver.add(S + 60 <= 1020)

    # Betty's blocked intervals
    betty_blocked = {
        0: [(600, 630), (690, 750), (960, 990)],  # Monday
        1: [(570, 600), (630, 660), (720, 750), (810, 930), (990, 1020)],  # Tuesday
        2: [(810, 840), (870, 900)],  # Wednesday
        3: [(540, 600), (690, 720), (750, 780), (810, 840), (870, 900)],  # Thursday
        4: [(540, 600), (690, 720), (750, 780), (870, 900)]  # Friday
    }

    # Megan's blocked intervals
    megan_blocked = {
        0: [(540, 1020)],  # Monday
        1: [(540, 570), (600, 630), (720, 840), (900, 930), (960, 990)],  # Tuesday
        2: [(570, 630), (660, 690), (750, 810), (810, 930), (990, 1020)],  # Wednesday
        3: [(540, 630), (690, 840), (870, 900), (990, 1020)],  # Thursday
        4: [(540, 1020)]  # Friday
    }

    # Add constraints for Betty's blocked times
    for day in betty_blocked:
        for start_block, end_block in betty_blocked[day]:
            solver.add(z3.Implies(Day == day, z3.Or(S >= end_block, S + 60 <= start_block)))

    # Add constraints for Megan's blocked times
    for day in megan_blocked:
        for start_block, end_block in megan_blocked[day]:
            solver.add(z3.Implies(Day == day, z3.Or(S >= end_block, S + 60 <= start_block)))

    # Betty's preferences: Do not meet on Wednesday or Thursday
    solver.add(Day != 2)
    solver.add(Day != 3)

    # Solve the constraints
    if solver.check() == z3.sat:
        model = solver.model()
        day = model[Day].as_long()
        start = model[S].as_long()
        end = start + 60

        # Convert minutes to HH:MM format
        def to_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"

        day_str = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"][day]
        print(f"Day: {day_str}")
        print(f"Start time: {to_time(start)}")
        print(f"End time: {to_time(end)}")
    else:
        print("No solution found.")

schedule_meeting()