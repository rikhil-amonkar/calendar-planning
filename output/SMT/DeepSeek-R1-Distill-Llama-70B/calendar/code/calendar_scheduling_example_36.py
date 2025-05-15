import z3

def schedule_meeting():
    solver = z3.Solver()
    S = z3.Int('S')  # Start time in minutes since midnight

    # Work hours constraint: 9:00 (540) to 17:00 (1020)
    solver.add(S >= 540)  # 9:00 AM
    solver.add(S <= 960)  # 16:00 to allow for 1-hour meeting

    # Blocked intervals for Ryan and Denise in minutes since midnight
    blocked = [
        # Ryan's blocks
        (540, 570), (750, 780),
        # Denise's blocks
        (570, 630), (720, 780), (870, 990)
    ]

    # Add constraints for each blocked interval
    for a, b in blocked:
        solver.add(z3.Or(S >= b, S + 60 <= a))

    # Denise's preference: Do not meet after 12:30 (750 minutes)
    solver.add(S <= 750)

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