import z3

def schedule_meeting():
    solver = z3.Solver()
    t = z3.Int('t')
    
    # Work hours constraint: 9:00 to 17:00 (540 to 1020 minutes)
    solver.add(t >= 540)  # 9:00
    solver.add(t <= 960)  # 17:00 - 60 minutes
    
    # Busy intervals in minutes (start, end)
    busy_intervals = [
        # James' busy times
        (690, 720),  # 11:30-12:00
        (870, 900),  # 14:30-15:00
        # John's busy times
        (570, 660),  # 9:30-11:00
        (690, 720),  # 11:30-12:00
        (750, 810),  # 12:30-13:30
        (870, 990)   # 14:30-16:30
    ]
    
    # Add constraints for each busy interval
    for s, e in busy_intervals:
        solver.add(z3.Or(t + 60 <= s, t >= e))
    
    # Solve the constraints
    if solver.check() == z3.sat:
        model = solver.model()
        start_time = model[t].as_long()
        # Convert start time back to hours:minutes format
        hours = start_time // 60
        minutes = start_time % 60
        print(f"Meeting can be scheduled from {hours:02d}:{minutes:02d} to {hours:02d}:{minutes:02d} +1 hour")
    else:
        print("No solution found.")

schedule_meeting()