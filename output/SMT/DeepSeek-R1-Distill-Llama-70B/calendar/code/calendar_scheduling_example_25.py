import z3

def schedule_meeting():
    solver = z3.Solver()
    S = z3.Int('S')  # Start time in minutes since midnight

    # Work hours constraint: 9:00 (540) to 17:00 (1020)
    solver.add(S >= 540)
    solver.add(S + 60 <= 1020)

    # Pamela's preference: latest start time is 13:30 (810 minutes)
    solver.add(S <= 810)

    # Blocked intervals for Anthony
    anthony_blocked = [
        (570, 600),  # 9:30-10:00
        (720, 780),  # 12:00-13:00
        (960, 990)   # 16:00-16:30
    ]

    # Blocked intervals for Pamela
    pamela_blocked = [
        (570, 600),  # 9:30-10:00
        (990, 1020)  # 16:30-17:00
    ]

    # Blocked intervals for Zachary
    zachary_blocked = [
        (540, 690),  # 9:00-11:30
        (720, 750),  # 12:00-12:30
        (780, 810),  # 13:00-13:30
        (870, 900),  # 14:30-15:00
        (960, 1020)  # 16:00-17:00
    ]

    # Add constraints for each participant's blocked times
    def add_constraints(blocked_intervals):
        for a, b in blocked_intervals:
            solver.add(z3.Or(S >= b, S + 60 <= a))

    add_constraints(anthony_blocked)
    add_constraints(pamela_blocked)
    add_constraints(zachary_blocked)

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