import z3

def schedule_meeting():
    solver = z3.Solver()
    t = z3.Int('t')
    
    # Work hours constraint: 9:00 to 17:00 (540 to 1020 minutes)
    solver.add(t >= 540)  # 9:00 AM
    solver.add(t + 30 <= 1020)  # Meeting ends by 5:00 PM
    
    # Janice's preference: No meetings after 13:00 (780 minutes)
    solver.add(t <= 780)  # Meeting starts by 13:00
    
    # Busy intervals in minutes (start, end)
    busy_intervals = [
        # Christine's busy times
        (570, 630),  # 9:30-10:30
        (720, 750),  # 12:00-12:30
        (780, 810),  # 13:00-13:30
        (870, 900),  # 14:30-15:00
        (960, 990),  # 16:00-16:30
        # Bobby's busy times
        (720, 750),  # 12:00-12:30
        (870, 900),  # 14:30-15:00
        # Elizabeth's busy times
        (540, 570),  # 9:00-9:30
        (690, 780),  # 11:30-13:00
        (780, 810),  # 13:30-14:00
        (900, 930),  # 15:00-15:30
        (960, 1020), # 16:00-17:00
        # Tyler's busy times
        (540, 660),  # 9:00-11:00
        (720, 750),  # 12:00-12:30
        (780, 810),  # 13:00-13:30
        (930, 960),  # 15:30-16:00
        (990, 1020), # 16:30-17:00
        # Edward's busy times
        (540, 570),  # 9:00-9:30
        (600, 660),  # 10:00-11:00
        (690, 840),  # 11:30-14:00
        (870, 930),  # 14:30-15:30
        (960, 1020)  # 16:00-17:00
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