import z3

def schedule_meeting():
    solver = z3.Solver()
    S = z3.Int('S')  # Start time in minutes since midnight

    # Work hours constraint: 9:00 (540) to 17:00 (1020)
    solver.add(S >= 540)  # 9:00 AM
    solver.add(S <= 990)  # 16:30 to allow for 30-minute meeting

    # Blocked intervals for Cynthia, Ann, Catherine, and Kyle in minutes since midnight
    blocked = [
        # Cynthia's blocks
        (540, 570), (600, 630), (810, 840), (900, 960),
        # Ann's blocks
        (600, 660), (780, 810), (840, 900), (960, 990),
        # Catherine's blocks
        (540, 690), (750, 810), (870, 1020),
        # Kyle's blocks
        (540, 570), (600, 690), (720, 750), (780, 870), (900, 960)
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