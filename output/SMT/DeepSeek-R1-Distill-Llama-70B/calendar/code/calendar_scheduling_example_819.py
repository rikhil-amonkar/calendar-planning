import z3

def schedule_meeting():
    solver = z3.Solver()
    Day = z3.Int('Day')    # 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday
    S = z3.Int('S')        # Start time in minutes since midnight

    # Work hours constraint: 9:00 (540) to 17:00 (1020)
    solver.add(S >= 540)
    solver.add(S + 30 <= 1020)

    # Ruth's blocked intervals
    ruth_blocked = {
        0: [(540, 1020)],  # Monday
        1: [(540, 1020)],  # Tuesday
        2: [(540, 1020)],  # Wednesday
        3: [(540, 660), (690, 870), (900, 1020)]  # Thursday: 9:00-11:00, 11:30-14:30, 15:00-17:00
    }

    # Add constraints for Ruth's blocked times
    for day in ruth_blocked:
        for start_block, end_block in ruth_blocked[day]:
            solver.add(z3.Implies(z3.And(Day == day, S >= start_block, S < end_block), z3.Or(S >= end_block, S + 30 <= start_block)))

    # Prefer Thursday and start time after 11:30 (690 minutes)
    solver.add(Day == 3)
    solver.add(S >= 690)

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

        day_str = ["Monday", "Tuesday", "Wednesday", "Thursday"][day]
        print(f"Day: {day_str}")
        print(f"Start time: {to_time(start)}")
        print(f"End time: {to_time(end)}")
    else:
        print("No solution found.")

schedule_meeting()