import z3

def schedule_meeting():
    solver = z3.Solver()
    t = z3.Int('t')
    
    # Work hours constraint: 9:00 to 17:00 (540 to 1020 minutes)
    solver.add(t >= 540)  # 9:00 AM
    solver.add(t <= 990)  # 4:30 PM (meeting ends by 5:00 PM)
    
    # Busy intervals in minutes (start, end)
    busy_intervals = [
        # Nancy's busy times
        # Monday
        (600, 630),  # 10:00-10:30
        (690, 750),  # 11:30-12:30
        (810, 840),  # 13:30-14:00
        (870, 930),  # 14:30-15:30
        (960, 1020), # 16:00-17:00
        # Tuesday
        (570, 630),  # 9:30-10:30
        (660, 690),  # 11:00-11:30
        (720, 750),  # 12:00-12:30
        (780, 810),  # 13:00-13:30
        (930, 960),  # 15:30-16:00
        # Wednesday
        (600, 810),  # 10:00-11:30
        (810, 960)   # 13:30-16:00
        ,
        # Jose's busy times
        # Monday
        (540, 1020), # 9:00-17:00
        # Tuesday
        (540, 1020), # 9:00-17:00
        # Wednesday
        (540, 570),  # 9:00-9:30
        (600, 750),  # 10:00-12:30
        (810, 870),  # 13:30-14:30
        (900, 1020)  # 15:00-17:00
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