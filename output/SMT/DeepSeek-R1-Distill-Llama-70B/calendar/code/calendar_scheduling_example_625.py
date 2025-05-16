import z3

def schedule_meeting():
    solver = z3.Solver()
    Day = z3.Int('Day')    # 0 for Monday, 1 for Tuesday
    S = z3.Int('S')        # Start time in minutes since midnight

    # Define work hours constraint
    solver.add(S >= 540)    # 9:00 AM
    solver.add(S <= 1020)   # 17:00 (5:00 PM)

    # Blocked intervals for Harold in minutes since midnight
    harold_blocked = {
        0: [(540, 600), (630, 1020)],  # Monday blocked times
        1: [(540, 570), (630, 690), (750, 810), (870, 930), (1020, 1020)]  # Tuesday blocked times
    }

    # Add constraints for each day
    for day in [0, 1]:
        blocked_intervals = harold_blocked[day]
        for start_block, end_block in blocked_intervals:
            # If the meeting is on this day, ensure it doesn't overlap with blocked times
            solver.add(z3.Implies(Day == day, z3.Or(S >= end_block, S + 30 <= start_block)))

    # Prefer Tuesday before 14:30
    solver.add(S <= 870)  # 14:30 in minutes since midnight

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

        day_str = "Monday" if day == 0 else "Tuesday"
        print(f"Day: {day_str}")
        print(f"Start time: {to_time(start)}")
        print(f"End time: {to_time(end)}")
    else:
        print("No solution found.")

schedule_meeting()