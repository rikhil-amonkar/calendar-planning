import z3

def schedule_meeting():
    solver = z3.Solver()
    S = z3.Int('S')  # Start time in minutes since midnight

    # Work hours constraint: 9:00 (540) to 17:00 (1020)
    # Meeting must end by 17:00, so latest start time is 990 (16:30)
    solver.add(S >= 540)    # 9:00 AM
    solver.add(S <= 990)    # 16:30

    # Christine's blocked intervals in minutes since midnight
    christine_blocked = [
        (570, 630),  # 9:30-10:30
        (720, 750),  # 12:00-12:30
        (780, 810),  # 13:00-13:30
        (870, 900),  # 14:30-15:00
        (960, 990)   # 16:00-16:30
    ]

    # Bobby's blocked intervals in minutes since midnight
    bobby_blocked = [
        (720, 750),  # 12:00-12:30
        (870, 900)   # 14:30-15:00
    ]

    # Elizabeth's blocked intervals in minutes since midnight
    elizabeth_blocked = [
        (540, 570),  # 9:00-9:30
        (690, 780),  # 11:30-13:00
        (780, 810),  # 13:30-14:00
        (900, 930),  # 15:00-15:30
        (960, 1020)  # 16:00-17:00
    ]

    # Tyler's blocked intervals in minutes since midnight
    tyler_blocked = [
        (540, 660),  # 9:00-11:00
        (720, 750),  # 12:00-12:30
        (780, 810),  # 13:00-13:30
        (930, 960),  # 15:30-16:00
        (990, 1020)  # 16:30-17:00
    ]

    # Edward's blocked intervals in minutes since midnight
    edward_blocked = [
        (540, 570),  # 9:00-9:30
        (600, 660),  # 10:00-11:00
        (690, 840),  # 11:30-14:00
        (870, 930),  # 14:30-15:30
        (960, 1020)  # 16:00-17:00
    ]

    # Add constraints for each participant's blocked intervals
    def add_constraints(blocked_intervals):
        for a, b in blocked_intervals:
            solver.add(z3.Or(S >= b, S + 30 <= a))

    add_constraints(christine_blocked)
    add_constraints(bobby_blocked)
    add_constraints(elizabeth_blocked)
    add_constraints(tyler_blocked)
    add_constraints(edward_blocked)

    # Janice's preference: Do not meet after 13:00 (780 minutes)
    solver.add(S <= 780)

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