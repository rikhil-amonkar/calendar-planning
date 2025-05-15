import z3

def schedule_meeting():
    solver = z3.Solver()
    S = z3.Int('S')  # Start time in minutes since midnight

    # Work hours constraint: 9:00 (540) to 17:00 (1020)
    solver.add(S >= 540)
    solver.add(S + 30 <= 1020)

    # Blocked intervals for each participant in minutes since midnight
    blocked = [
        # Megan's blocks
        (540, 570), (600, 660), (720, 750),
        # Christine's blocks
        (540, 570), (690, 720), (780, 840), (930, 990),
        # Sara's blocks
        (690, 720), (870, 900),
        # Bruce's blocks
        (570, 600), (630, 720), (750, 840), (870, 900), (930, 990),
        # Kathryn's blocks
        (600, 930), (960, 990),
        # Billy's blocks
        (540, 570), (660, 690), (720, 840), (870, 930)
    ]

    # Add constraints for each blocked interval
    for a, b in blocked:
        solver.add(z3.Or(S >= b, S + 30 <= a))

    # Check for solution
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