import z3

def schedule_meeting():
    solver = z3.Solver()
    S = z3.Int('S')  # Start time in minutes since midnight

    # Work hours constraint: 9:00 (540) to 17:00 (1020)
    # Meeting must end by 17:00, so latest start time is 990 (16:30)
    solver.add(S >= 540)    # 9:00 AM
    solver.add(S <= 990)    # 16:30

    # Daniel's blocked intervals on Tuesday in minutes since midnight
    daniel_blocked = [
        (660, 720),  # 11:00-12:00
        (780, 810),  # 13:00-13:30
        (930, 960),  # 15:30-16:00
        (990, 1020)  # 16:30-17:00
    ]

    # Bradley's blocked intervals on Tuesday in minutes since midnight
    bradley_blocked = [
        (630, 660),  # 10:30-11:00
        (720, 780),  # 12:00-13:00
        (810, 840),  # 13:30-14:00
        (930, 990)   # 15:30-16:30
    ]

    # Add constraints for Daniel's blocked times
    for a, b in daniel_blocked:
        solver.add(z3.Or(S >= b, S + 30 <= a))

    # Add constraints for Bradley's blocked times
    for a, b in bradley_blocked:
        solver.add(z3.Or(S >= b, S + 30 <= a))

    # Bradley's preference: Do not meet on Tuesday before 12:00 (720 minutes)
    # So, the meeting must start at or after 12:00
    solver.add(S >= 720)

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

        print(f"Day: Tuesday")
        print(f"Start time: {to_time(start)}")
        print(f"End time: {to_time(end)}")
    else:
        print("No solution found.")

schedule_meeting()