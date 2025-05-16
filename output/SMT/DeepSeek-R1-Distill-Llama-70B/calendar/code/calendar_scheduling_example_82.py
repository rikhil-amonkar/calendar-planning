import z3

def schedule_meeting():
    solver = z3.Solver()
    S = z3.Int('S')  # Start time in minutes since midnight

    # Work hours constraint: 9:00 (540) to 17:00 (1020)
    # Meeting must end by 17:00, so latest start time is 990 (16:30)
    solver.add(S >= 540)    # 9:00 AM
    solver.add(S <= 990)    # 16:30

    # Michael's blocked intervals in minutes since midnight
    michael_blocked = [
        (570, 630),  # 9:30-10:30
        (900, 930),  # 15:00-15:30
        (960, 990)   # 16:00-16:30
    ]

    # Arthur's blocked intervals in minutes since midnight
    arthur_blocked = [
        (540, 720),  # 9:00-12:00
        (780, 900),  # 13:00-15:00
        (930, 960),  # 15:30-16:00
        (990, 1020)  # 16:30-17:00
    ]

    # Add constraints for Michael's blocked times
    for a, b in michael_blocked:
        solver.add(z3.Or(S >= b, S + 30 <= a))

    # Add constraints for Arthur's blocked times
    for a, b in arthur_blocked:
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