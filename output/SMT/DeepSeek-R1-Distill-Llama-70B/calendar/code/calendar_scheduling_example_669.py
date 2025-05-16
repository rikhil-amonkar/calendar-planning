import z3

def schedule_meeting():
    solver = z3.Solver()
    Day = z3.Int('Day')    # 0: Monday, 1: Tuesday
    S = z3.Int('S')        # Start time in minutes since midnight

    # Work hours constraint: 9:00 (540) to 17:00 (1020)
    # Meeting must end by 17:00, so latest start time is 990 (16:30)
    solver.add(S >= 540)    # 9:00 AM
    solver.add(S <= 990)    # 16:30

    # Jean's blocked intervals on Tuesday
    jean_blocked = [
        (690, 720),  # 11:30-12:00
        (960, 990)   # 16:00-16:30
    ]

    # Doris's blocked intervals on Monday
    doris_monday_blocked = [
        (540, 690),  # 9:00-11:30
        (720, 750),  # 12:00-12:30
        (810, 900),  # 13:30-16:00
        (990, 1020)  # 16:30-17:00
    ]

    # Doris's blocked intervals on Tuesday
    doris_tuesday_blocked = [
        (540, 1020)  # 9:00-17:00
    ]

    # Add constraints for Jean's blocked times
    for day in [1]:  # Tuesday
        for start_block, end_block in jean_blocked:
            solver.add(z3.Implies(Day == day, z3.Or(S >= end_block, S + 30 <= start_block)))

    # Add constraints for Doris's blocked times on Monday
    for start_block, end_block in doris_monday_blocked:
        solver.add(z3.Implies(Day == 0, z3.Or(S >= end_block, S + 30 <= start_block)))

    # Add constraints for Doris's blocked times on Tuesday
    for start_block, end_block in doris_tuesday_blocked:
        solver.add(z3.Implies(Day == 1, z3.Or(S >= end_block, S + 30 <= start_block)))

    # Doris's preference: Do not meet on Monday after 14:00 (840 minutes)
    solver.add(z3.Implies(Day == 0, S <= 840))

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