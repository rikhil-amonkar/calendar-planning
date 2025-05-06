import z3

def schedule_meeting():
    solver = z3.Solver()
    t = z3.Int('t')
    
    # Work hours constraint: 9:00 to 17:00 (540 to 1020 minutes)
    solver.add(t >= 540)  # 9:00 AM
    solver.add(t + 60 <= 1020)  # Meeting ends by 5:00 PM
    
    # Busy intervals in minutes (start, end)
    busy_intervals = [
        # Patricia's busy times on Tuesday
        (600, 630),  # 10:00-10:30
        (660, 720),  # 11:00-12:00
        (840, 960),  # 14:00-16:00
        (990, 1020), # 16:30-17:00
        # Jesse's busy times on Tuesday
        (660, 690),  # 11:00-11:30
        (720, 750),  # 12:00-12:30
        (780, 840),  # 13:00-14:00
        (870, 900),  # 14:30-15:00
        (930, 1020)  # 15:30-17:00
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