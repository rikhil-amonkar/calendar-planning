import z3

def schedule_meeting():
    solver = z3.Solver()
    t = z3.Int('t')
    
    # Work hours constraint: 9:00 to 17:00 (540 to 1020 minutes)
    solver.add(t >= 540)  # 9:00 AM
    solver.add(t + 30 <= 1020)  # Meeting ends by 5:00 PM
    
    # Margaret's preference: No meetings before 14:30 (870 minutes)
    solver.add(t >= 870)  # Meeting starts at or after 14:30
    
    # Busy intervals in minutes (start, end)
    busy_intervals = [
        # Shirley's busy times
        (630, 660),  # 10:30-11:00
        (720, 750),  # 12:00-12:30
        # Jacob's busy times
        (540, 570),  # 9:00-9:30
        (600, 630),  # 10:00-10:30
        (660, 690),  # 11:00-11:30
        (750, 810),  # 12:30-13:30
        (870, 900),  # 14:30-15:00
        # Stephen's busy times
        (690, 720),  # 11:30-12:00
        (750, 780),  # 12:30-13:00
        # Margaret's busy times
        (540, 570),  # 9:00-9:30
        (630, 750),  # 10:30-12:30
        (780, 810),  # 13:00-13:30
        (900, 930),  # 15:00-15:30
        (990, 1020), # 16:30-17:00
        # Mason's busy times
        (540, 600),  # 9:00-10:00
        (630, 660),  # 10:30-11:00
        (690, 750),  # 11:30-12:30
        (780, 810),  # 13:00-13:30
        (840, 870),  # 14:00-14:30
        (990, 1020)  # 16:30-17:00
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