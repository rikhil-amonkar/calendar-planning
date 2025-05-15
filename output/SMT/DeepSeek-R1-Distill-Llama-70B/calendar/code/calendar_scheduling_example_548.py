import z3

def schedule_meeting():
    solver = z3.Solver()
    S = z3.Int('S')  # Start time in minutes since midnight

    # Work hours constraint: 9:00 (540) to 17:00 (1020)
    # Meeting must end by 17:00, so latest start time is 990 (16:30)
    solver.add(S >= 540)  # 9:00 AM
    solver.add(S <= 990)  # 16:30 to allow for 30-minute meeting

    # Nicole's blocked intervals
    nicole_blocked = [
        (540, 600),  # 9:00-10:00
        (630, 990)   # 10:30-16:30
    ]

    # Add constraints for Nicole's blocked times
    for a, b in nicole_blocked:
        solver.add(z3.Or(S >= b, S + 30 <= a))

    # Preference: Do not meet before 16:00 (960 minutes)
    solver.add(S >= 960)  # 16:00 or later

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