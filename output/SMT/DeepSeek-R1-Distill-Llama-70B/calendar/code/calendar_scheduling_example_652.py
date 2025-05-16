import z3

def schedule_meeting():
    solver = z3.Solver()
    S = z3.Int('S')  # Start time in minutes since midnight

    # Work hours constraint: 9:00 (540) to 17:00 (1020)
    # Meeting must end by 17:00, so latest start time is 990 (16:30)
    solver.add(S >= 540)    # 9:00 AM
    solver.add(S <= 990)    # 16:30

    # Jesse's blocked intervals on Tuesday
    jesse_blocked = [
        (540, 570),  # 9:00-9:30
        (780, 810),  # 13:00-13:30
        (840, 900)   # 14:00-15:00
    ]

    # Lawrence's blocked intervals on Tuesday
    lawrence_blocked = [
        (570, 630),  # 9:30-10:30
        (690, 750),  # 11:30-12:30
        (780, 810),  # 13:00-13:30
        (870, 900),  # 14:30-15:00
        (930, 990)   # 15:30-16:30
    ]

    # Add constraints for Jesse's blocked times
    for a, b in jesse_blocked:
        solver.add(z3.Or(S >= b, S + 30 <= a))

    # Add constraints for Lawrence's blocked times
    for a, b in lawrence_blocked:
        solver.add(z3.Or(S >= b, S + 30 <= a))

    # Lawrence's preference: Do not meet after 16:30 (990 minutes)
    solver.add(S <= 990)

    # Minimize the start time to find the earliest availability
    solver.minimize(S)

    # Solve the constraints
    if solver.check() == z3.sat:
        model = solver.model()
        start = model[S].as_long()
        end = start + 30

        # Convert minutes to HH:MM format
        def to_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"

        print(f"Day: Tuesday")
        print(f"Start time: {to_time(start)}")
        print(f"End time: {to_time(end)}")
    else:
        print("No solution found.")

schedule_meeting()