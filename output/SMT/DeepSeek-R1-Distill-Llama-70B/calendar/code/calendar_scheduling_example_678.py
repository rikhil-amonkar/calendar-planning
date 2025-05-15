import z3

def schedule_meeting():
    solver = z3.Solver()
    S = z3.Int('S')  # Start time in minutes since midnight

    # Work hours constraint: 9:00 (540) to 17:00 (1020)
    # Meeting must end by 17:00, so latest start time is 960 (16:00)
    solver.add(S >= 540)    # 9:00 AM
    solver.add(S <= 960)    # 16:00

    # Russell's blocked intervals on Monday and Tuesday
    russell_blocked = [
        (630, 660),  # Monday: 10:30-11:00
        (780, 810)   # Tuesday: 13:00-13:30
    ]

    # Alexander's blocked intervals on Monday and Tuesday
    alexander_blocked = [
        (540, 690), (720, 930), (900, 1020),  # Monday: 9:00-11:30, 12:00-14:30, 15:00-17:00
        (540, 600), (780, 840), (900, 930), (960, 990)  # Tuesday: 9:00-10:00, 13:00-14:00, 15:00-15:30, 16:00-16:30
    ]

    # Add constraints for Russell's blocked times
    for a, b in russell_blocked:
        solver.add(z3.Or(S >= b, S + 60 <= a))

    # Add constraints for Alexander's blocked times
    for a, b in alexander_blocked:
        solver.add(z3.Or(S >= b, S + 60 <= a))

    # Russell's preference: Do not meet on Tuesday before 13:30 (810 minutes)
    # Since we're considering Tuesday, ensure S >= 810
    solver.add(S >= 810)

    # Solve the constraints
    if solver.check() == z3.sat:
        model = solver.model()
        start = model[S].as_long()
        end = start + 60

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