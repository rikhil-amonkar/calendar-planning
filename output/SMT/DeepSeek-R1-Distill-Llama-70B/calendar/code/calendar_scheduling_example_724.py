import z3

def schedule_meeting():
    solver = z3.Solver()
    t = z3.Int('t')
    
    # Work hours constraint: 9:00 to 17:00 (540 to 1020 minutes)
    solver.add(t >= 540)  # 9:00 AM
    solver.add(t <= 990)  # 4:30 PM (meeting ends by 5:00 PM)
    
    # Tyler's preference: No meetings before 16:00 on Monday (960 minutes)
    solver.add(t >= 960)  # Meeting starts at or after 16:00
    
    # Busy intervals in minutes (start, end)
    busy_intervals = [
        # Tyler's busy times
        # Tuesday
        (540, 570),  # 9:00-9:30
        (870, 900),  # 14:30-15:00
        # Wednesday
        (630, 660),  # 10:30-11:00
        (750, 780),  # 12:30-13:00
        (810, 840),  # 13:30-14:00
        (990, 1020), # 16:30-17:00
        # Ruth's busy times
        # Monday
        (540, 600),  # 9:00-10:00
        (630, 720),  # 10:30-12:00
        (750, 870),  # 12:30-14:30
        (900, 960),  # 15:00-16:00
        (990, 1020), # 16:30-17:00
        # Tuesday
        (540, 1020), # 9:00-17:00
        # Wednesday
        (540, 1020)  # 9:00-17:00
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