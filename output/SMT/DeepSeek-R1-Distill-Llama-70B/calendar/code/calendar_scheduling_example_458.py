import z3

def schedule_meeting():
    solver = z3.Solver()
    t = z3.Int('t')
    
    # Work hours constraint: 9:00 to 17:00 (540 to 990 minutes)
    solver.add(t >= 540)  # 9:00 AM
    solver.add(t + 30 <= 990)  # Meeting ends by 5:00 PM
    
    # Wayne's preference: No meetings before 14:00 (840 minutes)
    solver.add(t >= 840)  # Meeting starts at or after 14:00
    
    # Busy intervals in minutes (start, end)
    busy_intervals = [
        # Melissa's busy times
        (600, 660),  # 10:00-11:00
        (750, 840),  # 12:30-14:00
        (900, 930),  # 15:00-15:30
        # Gregory's busy times
        (750, 780),  # 12:30-13:00
        (930, 960),  # 15:30-16:00
        # Victoria's busy times
        (540, 570),  # 9:00-9:30
        (630, 690),  # 10:30-11:30
        (780, 840),  # 13:00-14:00
        (870, 900),  # 14:30-15:00
        (930, 990),  # 15:30-16:30
        # Thomas's busy times
        (600, 720),  # 10:00-12:00
        (750, 780),  # 12:30-13:00
        (870, 960),  # 14:30-16:00
        # Jennifer's busy times
        (540, 570),  # 9:00-9:30
        (600, 630),  # 10:00-10:30
        (660, 780),  # 11:00-13:00
        (810, 870),  # 13:30-14:30
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