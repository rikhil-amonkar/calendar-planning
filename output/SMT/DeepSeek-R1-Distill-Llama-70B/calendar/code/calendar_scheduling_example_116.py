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
        # Adam's block
        (840, 900),  # 14:00-15:00
        # John's blocks
        (780, 810), (840, 870), (930, 960), (990, 1020),  # 13:00-13:30, 14:00-14:30, 15:30-16:00, 16:30-17:00
        # Stephanie's blocks
        (570, 600), (630, 660), (690, 960), (990, 1020),  # 9:30-10:00, 10:30-11:00, 11:30-16:00, 16:30-17:00
        # Anna's blocks
        (570, 600), (720, 750), (780, 930), (990, 1020)  # 9:30-10:00, 12:00-12:30, 13:00-15:30, 16:30-17:00
    ]

    # Add constraints for each blocked interval
    for a, b in blocked:
        solver.add(z3.Or(S >= b, S + 30 <= a))

    # Anna's preference: Do not meet before 14:30 (870 minutes)
    solver.add(S >= 870)

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