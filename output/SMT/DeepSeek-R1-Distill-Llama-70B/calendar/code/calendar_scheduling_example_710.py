import z3

def schedule_meeting():
    solver = z3.Solver()
    Day = z3.Int('Day')    # 0: Monday, 1: Tuesday, 2: Wednesday
    S = z3.Int('S')        # Start time in minutes since midnight

    # Work hours constraint: 9:00 (540) to 17:00 (1020)
    solver.add(S >= 540)
    solver.add(S + 30 <= 1020)

    # Cheryl's blocked intervals
    cheryl_blocked = {
        0: [(540, 570), (690, 780), (930, 960)],  # Monday
        1: [(900, 930)],                           # Tuesday
        2: []                                        # Wednesday (cannot meet)
    }

    # Kyle's blocked intervals
    kyle_blocked = {
        0: [(540, 1020)],           # Monday
        1: [(570, 1020)],           # Tuesday
        2: [(540, 570), (600, 780), (810, 840), (870, 1020)]  # Wednesday
    }

    # Add constraints for Cheryl's blocked times
    for day in cheryl_blocked:
        for start_block, end_block in cheryl_blocked[day]:
            solver.add(z3.Implies(z3.And(Day == day, S >= start_block, S < end_block), z3.Or(S >= end_block, S + 30 <= start_block)))

    # Add constraints for Kyle's blocked times
    for day in kyle_blocked:
        for start_block, end_block in kyle_blocked[day]:
            solver.add(z3.Implies(z3.And(Day == day, S >= start_block, S < end_block), z3.Or(S >= end_block, S + 30 <= start_block)))

    # Prefer earliest availability
    solver.add(S <= 570)  # 9:30 AM

    # Check for solution
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