import z3

def schedule_meeting():
    solver = z3.Solver()
    t = z3.Int('t')
    
    # Work hours constraint: 9:00 to 17:00 (540 to 1020 minutes)
    solver.add(t >= 540)  # 9:00 AM
    solver.add(t + 30 <= 1020)  # Meeting ends by 5:00 PM
    
    # Priority to Tuesday and Wednesday (t < 1440 and t < 1500)
    solver.add(t < 1440)  # Ensure meeting is on Tuesday or Wednesday
    
    # Busy intervals in minutes (start, end)
    busy_intervals = [
        # Robert's busy times
        # Monday
        (660, 690),  # 11:00-11:30
        (840, 870),  # 14:00-14:30
        (930, 960),  # 15:30-16:00
        # Tuesday
        (630, 660),  # 10:30-11:00
        (900, 930),  # 15:00-15:30
        # Wednesday
        (600, 660),  # 10:00-11:00
        (690, 720),  # 11:30-12:00
        (750, 780),  # 12:30-13:00
        (810, 840),  # 13:30-14:00
        (900, 930),  # 15:00-15:30
        (960, 990),  # 16:00-16:30
        # Ralph's busy times
        # Monday
        (600, 810),  # 10:00-13:30
        (840, 870),  # 14:00-14:30
        (900, 1020), # 15:00-17:00
        # Tuesday
        (540, 570),  # 9:00-9:30
        (600, 630),  # 10:00-10:30
        (660, 690),  # 11:00-11:30
        (720, 780),  # 12:00-13:00
        (840, 930),  # 14:00-15:30
        (960, 1020), # 16:00-17:00
        # Wednesday
        (630, 660),  # 10:30-11:00
        (690, 720),  # 11:30-12:00
        (780, 870),  # 13:00-14:30
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