import z3

def schedule_meeting():
    solver = z3.Solver()
    S = z3.Int('S')  # Start time in minutes since midnight

    # Work hours constraint: 9:00 (540) to 17:00 (1020)
    solver.add(S >= 540)
    solver.add(S + 30 <= 1020)

    # Blocked intervals for Jack and Charlotte in minutes since midnight
    jack_blocked = [
        (570, 600),  # 9:30-10:30
        (660, 690),  # 11:00-11:30
        (750, 780),  # 12:30-13:00
        (840, 870),  # 14:00-14:30
        (960, 990)   # 16:00-16:30
    ]

    charlotte_blocked = [
        (570, 600),  # 9:30-10:00
        (630, 720),  # 10:30-12:00
        (750, 810),  # 12:30-13:30
        (840, 960)   # 14:00-16:00
    ]

    # Add constraints for Jack's blocked intervals
    for a, b in jack_blocked:
        solver.add(z3.Or(S >= b, S + 30 <= a))

    # Add constraints for Charlotte's blocked intervals
    for a, b in charlotte_blocked:
        solver.add(z3.Or(S >= b, S + 30 <= a))

    # Prefer meeting before 12:30 (750 minutes)
    solver.add(S < 750)

    # Check for solution
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