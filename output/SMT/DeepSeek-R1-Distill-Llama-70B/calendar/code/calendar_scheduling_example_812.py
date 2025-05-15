import z3

def schedule_meeting():
    solver = z3.Solver()
    Day = z3.Int('Day')    # 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday
    S = z3.Int('S')        # Start time in minutes since midnight

    # Work hours constraint: 9:00 (540) to 17:00 (1020)
    # Meeting must end by 17:00, so latest start time is 990 (16:30)
    solver.add(S >= 540)    # 9:00 AM
    solver.add(S <= 990)    # 16:30

    # Mary's blocked intervals
    mary_blocked = {
        1: [(600, 630), (930, 960)],      # Tuesday: 10:00-10:30, 15:30-16:00
        2: [(570, 600), (900, 930)],      # Wednesday: 9:30-10:00, 15:00-15:30
        3: [(540, 600), (630, 750)]       # Thursday: 9:00-10:00, 10:30-11:30
    }

    # Alexis's blocked intervals
    alexis_blocked = {
        0: [(540, 600), (630, 720), (750, 990)],  # Monday: 9:00-10:00, 10:30-12:00, 12:30-16:30
        1: [(540, 600), (630, 750), (900, 1020)],  # Tuesday: 9:00-10:00, 10:30-11:30, 12:00-15:30, 16:00-17:00
        2: [(540, 660), (690, 1020)],              # Wednesday: 9:00-11:00, 11:30-17:00
        3: [(600, 720), (840, 870), (930, 960), (990, 1020)]  # Thursday: 10:00-12:00, 14:00-14:30, 15:30-16:00, 16:30-17:00
    }

    # Add constraints for Mary's blocked times
    for day in mary_blocked:
        for start_block, end_block in mary_blocked[day]:
            solver.add(z3.Implies(z3.And(Day == day, S >= start_block, S < end_block), z3.Or(S >= end_block, S + 30 <= start_block)))

    # Add constraints for Alexis's blocked times
    for day in alexis_blocked:
        for start_block, end_block in alexis_blocked[day]:
            solver.add(z3.Implies(z3.And(Day == day, S >= start_block, S < end_block), z3.Or(S >= end_block, S + 30 <= start_block)))

    # Minimize the start time to find the earliest availability
    solver.minimize(S)

    # Solve the constraints
    if solver.check() == z3.sat:
        model = solver.model()
        day = model[Day].as_long()
        start = model[S].as_long()
        end = start + 30

        # Convert minutes to HH:MM format
        def to_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"

        day_str = ["Monday", "Tuesday", "Wednesday", "Thursday"][day]
        print(f"Day: {day_str}")
        print(f"Start time: {to_time(start)}")
        print(f"End time: {to_time(end)}")
    else:
        print("No solution found.")

schedule_meeting()