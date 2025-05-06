import z3

def schedule_meeting():
    solver = z3.Solver()
    t = z3.Int('t')
    
    # Work hours constraint: 9:00 to 17:00 (540 to 1020 minutes)
    solver.add(t >= 540)  # 9:00 AM
    solver.add(t <= 990)  # 4:30 PM (meeting ends by 5:00 PM)
    
    # Pamela's preferences: No meetings before 16:00 on Wednesday
    solver.add(t >= 960)  # Meeting starts after 16:00
    
    # Busy intervals in minutes (start, end)
    busy_intervals = [
        # Amy's busy times on Wednesday
        (660, 690),  # 11:00-11:30
        (810, 840),  # 13:30-14:00
        # Pamela's busy times on Wednesday
        (540, 570),  # 9:00-9:30
        (600, 660),  # 10:00-11:00
        (690, 810),  # 11:30-13:30
        (870, 900),  # 14:30-15:00
        (960, 990)   # 16:00-16:30
    ]
    
    # Add constraints for each busy interval
    for s, e in busy_intervals:
        solver.add(z3.Or(t + 30 <= s, t >= e))
    
    # Solve the constraints
    if solver.check() == z3.sat:
        model = solver.model()
        start_time = model[t].as_long()
        # Convert start time back to hours:minutes format
        hours = start_time // 60
        minutes = start_time % 60
        end_hours = (start_time + 30) // 60
        end_minutes = (start_time + 30) % 60
        print(f"Meeting can be scheduled from {hours:02d}:{minutes:02d} to {end_hours:02d}:{end_minutes:02d}")
    else:
        print("No solution found.")

schedule_meeting()