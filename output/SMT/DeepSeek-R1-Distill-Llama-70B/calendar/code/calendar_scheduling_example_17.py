import z3

def schedule_meeting():
    solver = z3.Solver()
    S = z3.Int('S')  # Start time in minutes since midnight

    # Work hours constraint: 9:00 (540) to 17:00 (1020)
    # Meeting must end by 17:00, so latest start time is 990 (16:30)
    solver.add(S >= 540)    # 9:00 AM
    solver.add(S <= 990)    # 16:30

    # Margaret's blocked intervals in minutes since midnight
    margaret_blocked = [
        (540, 600),  # 9:00-10:00
        (630, 660),  # 10:30-11:00
        (690, 720),  # 11:30-12:00
        (780, 810),  # 13:00-13:30
        (900, 930)   # 15:00-15:30
    ]

    # Donna's blocked intervals in minutes since midnight
    donna_blocked = [
        (870, 900),  # 14:30-15:00
        (960, 990)   # 16:00-16:30
    ]

    # Helen's blocked intervals in minutes since midnight
    helen_blocked = [
        (540, 570),  # 9:00-9:30
        (600, 690),  # 10:00-11:30
        (780, 840),  # 13:00-14:00
        (870, 900),  # 14:30-15:00
        (930, 1020)  # 15:30-17:00
    ]

    # Add constraints for Margaret's blocked times
    for a, b in margaret_blocked:
        solver.add(z3.Or(S >= b, S + 30 <= a))

    # Add constraints for Donna's blocked times
    for a, b in donna_blocked:
        solver.add(z3.Or(S >= b, S + 30 <= a))

    # Add constraints for Helen's blocked times
    for a, b in helen_blocked:
        solver.add(z3.Or(S >= b, S + 30 <= a))

    # Helen's preference: Do not meet after 13:30 (810 minutes)
    solver.add(S <= 810)

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

        print(f"Day: Monday")
        print(f"Start time: {to_time(start)}")
        print(f"End time: {to_time(end)}")
    else:
        print("No solution found.")

schedule_meeting()