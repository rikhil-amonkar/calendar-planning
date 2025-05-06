import z3

def schedule_meeting():
    solver = z3.Solver()
    t = z3.Int('t')
    
    # Work hours constraint: 9:00 to 17:00 (540 to 1020 minutes)
    solver.add(t >= 540)  # 9:00 AM
    solver.add(t <= 1020 - 60)  # Meeting ends by 17:00
    
    # Pamela's constraint: Meeting must end by 14:30 (810 minutes)
    solver.add(t + 60 <= 810)  # t <= 750
    
    # Busy intervals in minutes (start, end)
    busy_intervals = [
        # Anthony's busy times
        (570, 600),  # 9:30-10:00
        (720, 780),  # 12:00-13:00
        (960, 990),  # 16:00-16:30
        # Pamela's busy times
        (570, 600),  # 9:30-10:00
        (990, 1020), # 16:30-17:00
        # Zachary's busy times
        (540, 690),  # 9:00-11:30
        (720, 750),  # 12:00-12:30
        (780, 810),  # 13:00-13:30
        (870, 900),  # 14:30-15:00
        (960, 1020)  # 16:00-17:00
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
        end_hours = (start_time + 60) // 60
        end_minutes = (start_time + 60) % 60
        print(f"Meeting can be scheduled from {hours:02d}:{minutes:02d} to {end_hours:02d}:{end_minutes:02d}")
    else:
        print("No solution found.")

schedule_meeting()