import z3

def schedule_meeting():
    solver = z3.Solver()
    S = z3.Int('S')  # Start time in minutes since midnight

    # Work hours constraint: 9:00 (540) to 17:00 (1020)
    solver.add(S >= 540)  # 9:00 AM
    solver.add(S <= 990)  # 16:30 to allow for 30-minute meeting

    # Betty's blocked intervals on Wednesday in minutes since midnight
    betty_blocked = [
        (570, 630),  # 9:30-10:30
        (780, 810),  # 13:00-13:30
        (840, 870)   # 14:00-14:30
    ]

    # Scott's blocked intervals on Wednesday in minutes since midnight
    scott_blocked = [
        (570, 750),  # 9:30-12:30
        (780, 810),  # 13:00-13:30
        (840, 870),  # 14:00-14:30
        (900, 930),  # 15:00-15:30
        (960, 990)   # 16:00-16:30
    ]

    # Add constraints for Betty's blocked times
    for a, b in betty_blocked:
        solver.add(z3.Or(S >= b, S + 30 <= a))

    # Add constraints for Scott's blocked times
    for a, b in scott_blocked:
        solver.add(z3.Or(S >= b, S + 30 <= a))

    # Preference: Wednesday only and Scott's preference to avoid Wednesday
    # Since it's the only possible day, we proceed

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

        print(f"Day: Wednesday")
        print(f"Start time: {to_time(start)}")
        print(f"End time: {to_time(end)}")
    else:
        print("No solution found.")

schedule_meeting()