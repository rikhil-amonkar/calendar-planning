import z3

def schedule_meeting():
    solver = z3.Solver()
    Day = z3.Int('Day')    # 0: Monday, 1: Tuesday, 2: Wednesday
    S = z3.Int('S')        # Start time in minutes since midnight

    # Work hours constraint: 9:00 (540) to 17:00 (1020)
    # Meeting must end by 17:00, so latest start time is 960 (16:00)
    solver.add(S >= 540)    # 9:00 AM
    solver.add(S <= 960)    # 16:00

    # Roy's blocked intervals in minutes since midnight
    roy_blocked = {
        0: [(600, 690), (720, 780), (840, 870), (900, 1020)],  # Monday: 10:00-11:30, 12:00-13:00, 14:00-14:30, 15:00-17:00
        1: [(630, 690), (720, 870), (900, 930), (960, 1020)],   # Tuesday: 10:30-11:30, 12:00-14:30, 15:00-15:30, 16:00-17:00
        2: [(570, 690), (750, 840), (870, 930), (990, 1020)]    # Wednesday: 9:30-11:30, 12:30-14:00, 14:30-15:30, 16:30-17:00
    }

    # Add constraints for Roy's blocked times
    for day in roy_blocked:
        for start_block, end_block in roy_blocked[day]:
            solver.add(z3.Implies(z3.And(Day == day, S >= start_block, S < end_block), z3.Or(S >= end_block, S + 60 <= start_block)))

    # Minimize the start time to find the earliest availability
    solver.minimize(S)

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

        day_str = ["Monday", "Tuesday", "Wednesday"][day]
        print(f"Day: {day_str}")
        print(f"Start time: {to_time(start)}")
        print(f"End time: {to_time(end)}")
    else:
        print("No solution found.")

schedule_meeting()