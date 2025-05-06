import z3

def schedule_meeting():
    solver = z3.Solver()
    t = z3.Int('t')
    
    # Work hours constraint: 9:00 to 17:00 (540 to 1020 minutes)
    solver.add(t >= 540)  # 9:00 AM
    solver.add(t + 60 <= 1020)  # Meeting ends by 5:00 PM
    
    # Busy intervals in minutes (start, end)
    busy_intervals = [
        # Joshua's busy times
        (660, 750),  # 11:00-12:30
        (810, 870),  # 13:30-14:30
        (990, 1020), # 16:30-17:00
        # Jerry's busy times
        (540, 570),  # 9:00-9:30
        (630, 720),  # 10:30-12:00
        (750, 780),  # 12:30-13:00
        (810, 840),  # 13:30-14:00
        (870, 900),  # 14:30-15:00
        (930, 960),  # 15:30-16:00
        # Jesse's busy times
        (540, 570),  # 9:00-9:30
        (630, 720),  # 10:30-12:00
        (750, 780),  # 12:30-13:00
        (870, 900),  # 14:30-15:00
        (930, 990),  # 15:30-16:30
        # Kenneth's busy times
        (630, 750),  # 10:30-12:30
        (810, 840),  # 13:30-14:00
        (870, 900),  # 14:30-15:00
        (930, 960),  # 15:30-16:00
        (990, 1020)  # 16:30-17:00
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