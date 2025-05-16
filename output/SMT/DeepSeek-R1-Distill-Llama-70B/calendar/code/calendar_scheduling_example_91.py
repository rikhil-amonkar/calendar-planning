import z3

def schedule_meeting():
    solver = z3.Solver()
    S = z3.Int('S')  # Start time in minutes since midnight

    # Work hours constraint: 9:00 (540) to 17:00 (1020)
    # Meeting must end by 17:00, so latest start time is 960 (16:00)
    solver.add(S >= 540)    # 9:00 AM
    solver.add(S <= 960)    # 16:00

    # Blocked intervals for each participant in minutes since midnight
    blocked = [
        # Danielle's blocks
        (540, 600), (630, 660), (870, 900), (930, 960), (990, 1020),
        # Bruce's blocks
        (660, 690), (750, 780), (840, 870), (930, 960),
        # Eric's blocks
        (540, 570), (600, 660), (690, 780), (870, 930)
    ]

    # Add constraints for each blocked interval
    for a, b in blocked:
        solver.add(z3.Or(S >= b, S + 60 <= a))

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

        print(f"Day: Monday")
        print(f"Start time: {to_time(start)}")
        print(f"End time: {to_time(end)}")
    else:
        print("No solution found.")

schedule_meeting()