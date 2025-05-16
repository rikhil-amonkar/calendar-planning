import z3

def schedule_meeting():
    solver = z3.Solver()
    S = z3.Int('S')  # Start time in minutes since midnight

    # Constraint: Meeting must start between 9:00 (540) and 16:30 (990), but since Albert can't meet after 11:00, it must end by 11:00 (660)
    # So, latest start time is 630 (10:30) to allow for 30 minutes
    solver.add(S >= 540)  # 9:00
    solver.add(S <= 630)  # 10:30

    # Albert's blocked intervals
    # 1. 9:00 to 10:00 (540 to 600)
    # Meeting must start at or after 600
    solver.add(S >= 600)
    # 2. 10:30 to 12:00 (630 to 720)
    # Meeting must end before 630, so start before 630 - 30 = 600
    solver.add(S <= 600)

    # Solve the constraints
    if solver.check() == z3.sat:
        model = solver.model()
        start = model[S].as_long()
        end = start + 30

        # Function to convert minutes to HH:MM format
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