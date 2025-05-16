import z3

def schedule_meeting():
    solver = z3.Solver()
    S = z3.Int('S')  # Start time in minutes since midnight

    # Work hours constraint: 9:00 (540) to 17:00 (1020)
    # Meeting must end by 17:00, so latest start time is 990 (16:30)
    solver.add(S >= 540)    # 9:00 AM
    solver.add(S <= 990)    # 16:30

    # Blocked intervals for each participant in minutes since midnight
    blocked = [
        # Andrea's blocks
        (570, 600), (810, 840),
        # Ruth's blocks
        (750, 780), (900, 930),
        # Steven's blocks
        (600, 630), (660, 690), (720, 750), (810, 840), (900, 960),
        # Kyle's blocks
        (540, 570), (630, 720), (750, 780), (810, 900), (930, 960), (990, 1020),
        # Elijah's blocks
        (540, 660), (690, 780), (810, 840), (930, 960), (990, 1020),
        # Lori's blocks
        (540, 570), (600, 690), (720, 810), (840, 960), (990, 1020)
    ]

    # Add constraints for each blocked interval
    for a, b in blocked:
        solver.add(z3.Or(S >= b, S + 30 <= a))

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