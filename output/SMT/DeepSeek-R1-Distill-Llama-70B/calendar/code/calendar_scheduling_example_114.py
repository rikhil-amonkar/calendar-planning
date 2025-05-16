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
        # Stephanie's blocks
        (600, 630), (960, 990),  # 10:00-10:30, 16:00-16:30
        # Cheryl's blocks
        (600, 630), (690, 720), (810, 840), (990, 1020),  # 10:00-10:30, 11:30-12:00, 13:30-14:00, 16:30-17:00
        # Bradley's blocks
        (570, 600), (630, 750), (810, 840), (870, 900), (930, 1020),  # 9:30-10:00, 10:30-11:30, 13:30-14:00, 14:30-15:00, 15:30-17:00
        # Steven's blocks
        (540, 720), (780, 810), (870, 1020)  # 9:00-12:00, 13:00-13:30, 14:30-17:00
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