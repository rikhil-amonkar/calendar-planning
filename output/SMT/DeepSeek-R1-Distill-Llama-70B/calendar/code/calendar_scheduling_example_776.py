import z3

def schedule_meeting():
    solver = z3.Solver()
    S = z3.Int('S')  # Start time in minutes since midnight

    # Work hours constraint: 9:00 (540) to 17:00 (1020)
    # Meeting must end by 17:00, so latest start time is 990 (16:30)
    solver.add(S >= 540)    # 9:00 AM
    solver.add(S <= 990)    # 16:30

    # Jennifer's blocked intervals on Monday in minutes since midnight
    jennifer_blocked = [
        (540, 660),  # 9:00-11:00
        (690, 780),  # 11:30-13:00
        (810, 870),  # 13:30-14:30
        (900, 1020)  # 15:00-17:00
    ]

    # Add constraints for Jennifer's blocked times
    for a, b in jennifer_blocked:
        solver.add(z3.Or(S >= b, S + 30 <= a))

    # John's preferences: Do not meet on Monday after 14:30 (870 minutes)
    # So, the meeting must start by 14:30 (870 minutes)
    solver.add(S <= 870)

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