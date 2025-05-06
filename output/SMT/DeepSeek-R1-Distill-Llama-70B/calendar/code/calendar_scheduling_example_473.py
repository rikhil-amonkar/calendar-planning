import z3

def schedule_meeting():
    solver = z3.Solver()
    t = z3.Int('t')
    
    # Work hours constraint: 9:00 to 17:00 (540 to 1020 minutes)
    solver.add(t >= 540)  # 9:00 AM
    solver.add(t + 30 <= 1020)  # Meeting ends by 5:00 PM
    
    # Busy intervals in minutes (start, end)
    busy_intervals = [
        # Gregory
        (540, 570),  # 9:00-9:30
        (690, 720),  # 11:30-12:00
        # Jonathan
        (540, 570),  # 9:00-9:30
        (720, 750),  # 12:00-12:30
        (780, 810),  # 13:00-13:30
        (900, 960),  # 15:00-16:00
        (990, 1020), # 16:30-17:00
        # Barbara
        (600, 630),  # 10:00-10:30
        (810, 840),  # 13:30-14:00
        # Jesse
        (600, 660),  # 10:00-11:00
        (750, 870),  # 12:30-14:30
        # Alan
        (570, 660),  # 9:30-11:00
        (690, 750),  # 11:30-12:30
        (780, 930),  # 13:00-15:30
        (960, 1020), # 16:00-17:00
        # Nicole
        (540, 630),  # 9:00-10:30
        (690, 720),  # 11:30-12:00
        (750, 810),  # 12:30-13:30
        (840, 1020), # 14:00-17:00
        # Catherine
        (540, 630),  # 9:00-10:30
        (720, 810),  # 12:00-13:30
        (900, 930),  # 15:00-15:30
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