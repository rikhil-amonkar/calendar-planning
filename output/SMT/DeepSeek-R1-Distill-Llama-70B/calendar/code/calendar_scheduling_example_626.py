import z3

def schedule_meeting():
    solver = z3.Solver()
    Day = z3.Int('Day')    # 0: Monday, 1: Tuesday
    S = z3.Int('S')        # Start time in minutes since midnight

    # Work hours constraint: 9:00 (540) to 17:00 (1020)
    # Meeting must end by 17:00, so latest start time is 960 (16:00)
    solver.add(S >= 540)    # 9:00 AM
    solver.add(S <= 960)    # 16:00

    # Jesse is blocked all day on Monday, so meeting must be on Tuesday
    solver.add(Day == 1)

    # Patricia's blocked intervals on Tuesday
    patricia_blocked = [
        (600, 630),  # 10:00-10:30
        (660, 720),  # 11:00-12:00
        (840, 960),  # 14:00-16:00
        (990, 1020)  # 16:30-17:00
    ]

    # Jesse's blocked intervals on Tuesday
    jesse_blocked = [
        (660, 690),  # 11:00-11:30
        (720, 750),  # 12:00-12:30
        (780, 840),  # 13:00-14:00
        (870, 900),  # 14:30-15:00
        (930, 1020)  # 15:30-17:00
    ]

    # Add constraints for Patricia's blocked times
    for a, b in patricia_blocked:
        solver.add(z3.Or(S >= b, S + 60 <= a))

    # Add constraints for Jesse's blocked times
    for a, b in jesse_blocked:
        solver.add(z3.Or(S >= b, S + 60 <= a))

    # Solve the constraints
    if solver.check() == z3.sat:
        model = solver.model()
        day = model[Day].as_long()
        start = model[S].as_long()
        end = start + 60

        # Convert minutes to HH:MM format
        def to_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"

        day_str = ["Monday", "Tuesday"][day]
        print(f"Day: {day_str}")
        print(f"Start time: {to_time(start)}")
        print(f"End time: {to_time(end)}")
    else:
        print("No solution found.")

schedule_meeting()