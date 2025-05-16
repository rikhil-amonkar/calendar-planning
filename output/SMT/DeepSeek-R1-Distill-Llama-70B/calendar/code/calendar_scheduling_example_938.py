import z3

def schedule_meeting():
    solver = z3.Solver()
    Day = z3.Int('Day')    # 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday, 4: Friday
    S = z3.Int('S')        # Start time in minutes since midnight

    # Work hours constraint: 9:00 (540) to 17:00 (1020)
    # Meeting must end by 17:00, so latest start time is 990 (16:30)
    solver.add(S >= 540)    # 9:00 AM
    solver.add(S <= 990)    # 16:30

    # Eugene's blocked intervals
    eugene_blocked = {
        0: [(660, 720), (810, 840), (870, 900), (960, 990)],  # Monday: 11:00-12:00, 13:30-14:00, 14:30-15:00, 16:00-16:30
        2: [(540, 570), (660, 690), (720, 750), (810, 930)],    # Wednesday: 9:00-9:30, 11:00-11:30, 12:00-12:30, 13:30-15:00
        3: [(570, 600), (660, 750)],                           # Thursday: 9:30-10:00, 11:00-12:30
        4: [(630, 660), (720, 750), (780, 810)]                 # Friday: 10:30-11:00, 12:00-12:30, 13:00-13:30
    }

    # Eric's blocked intervals
    eric_blocked = {
        0: [(540, 1020)],  # Monday: 9:00-17:00
        1: [(540, 1020)],  # Tuesday: 9:00-17:00
        2: [(540, 690), (720, 840), (870, 990)],  # Wednesday: 9:00-11:30, 12:00-14:00, 14:30-16:30
        3: [(540, 1020)],  # Thursday: 9:00-17:00
        4: [(540, 660), (690, 1020)]  # Friday: 9:00-11:00, 11:30-17:00
    }

    # Add constraints for Eugene's blocked times
    for day in eugene_blocked:
        for start_block, end_block in eugene_blocked[day]:
            solver.add(z3.Implies(z3.And(Day == day, S >= start_block, S < end_block), z3.Or(S >= end_block, S + 30 <= start_block)))

    # Add constraints for Eric's blocked times
    for day in eric_blocked:
        for start_block, end_block in eric_blocked[day]:
            solver.add(z3.Implies(z3.And(Day == day, S >= start_block, S < end_block), z3.Or(S >= end_block, S + 30 <= start_block)))

    # Eric's preference: Do not meet on Wednesday
    solver.add(Day != 2)

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

        day_str = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"][day]
        print(f"Day: {day_str}")
        print(f"Start time: {to_time(start)}")
        print(f"End time: {to_time(end)}")
    else:
        print("No solution found.")

schedule_meeting()