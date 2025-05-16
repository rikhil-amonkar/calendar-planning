import z3

def schedule_meeting():
    solver = z3.Solver()
    Day = z3.Int('Day')    # 0: Monday, 1: Tuesday, 2: Wednesday
    S = z3.Int('S')        # Start time in minutes since midnight

    # Work hours constraint: 9:00 (540) to 17:00 (1020)
    solver.add(S >= 540)
    solver.add(S + 30 <= 1020)

    # Tyler's blocked intervals
    tyler_blocked = {
        0: [],             # Monday
        1: [(540, 570), (870, 900)],  # Tuesday: 9:00-9:30, 14:30-15:00
        2: [(630, 660), (750, 780), (810, 840), (990, 1020)]  # Wednesday: 10:30-11:00, 12:30-13:00, 13:30-14:00, 16:30-17:00
    }

    # Ruth's blocked intervals
    ruth_blocked = {
        0: [(540, 600), (630, 720), (750, 990), (1020, 1020)],  # Monday: 9:00-10:00, 10:30-12:00, 12:30-16:30, 17:00-17:00
        1: [(540, 1020)],  # Tuesday: 9:00-17:00
        2: [(540, 1020)]   # Wednesday: 9:00-17:00
    }

    # Add constraints for Tyler's blocked times
    for day in tyler_blocked:
        for start_block, end_block in tyler_blocked[day]:
            solver.add(z3.Implies(Day == day, z3.Or(S >= end_block, S + 30 <= start_block)))

    # Add constraints for Ruth's blocked times
    for day in ruth_blocked:
        for start_block, end_block in ruth_blocked[day]:
            solver.add(z3.Implies(z3.And(Day == day, S >= start_block, S < end_block), z3.Or(S >= end_block, S + 30 <= start_block)))

    # Prefer Monday after 16:00 (960 minutes)
    solver.add(Day == 0)  # Only consider Monday
    solver.add(S >= 960)  # 16:00 or later

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