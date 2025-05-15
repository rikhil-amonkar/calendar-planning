import z3

def schedule_meeting():
    solver = z3.Solver()
    S = z3.Int('S')  # Start time in minutes since midnight

    # Work hours constraint: 9:00 (540) to 17:00 (1020)
    # Meeting must end by 17:00, so latest start time is 990 (16:30)
    solver.add(S >= 540)    # 9:00 AM
    solver.add(S <= 990)    # 16:30

    # Ryan's blocked intervals on Monday in minutes since midnight
    ryan_blocked = [
        (570, 600),  # 9:30-10:00
        (660, 720),  # 11:00-12:00
        (780, 810),  # 13:00-13:30
        (930, 960)   # 15:30-16:00
    ]

    # Adam's blocked intervals on Monday in minutes since midnight
    adam_blocked = [
        (540, 630),  # 9:00-10:30
        (660, 810),  # 11:00-13:30
        (840, 960),  # 14:00-16:00
        (990, 1020)  # 16:30-17:00
    ]

    # Add constraints for Ryan's blocked times
    for a, b in ryan_blocked:
        solver.add(z3.Or(S >= b, S + 30 <= a))

    # Add constraints for Adam's blocked times
    for a, b in adam_blocked:
        solver.add(z3.Or(S >= b, S + 30 <= a))

    # Preference: Do not meet on Monday before 14:30 (870 minutes)
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