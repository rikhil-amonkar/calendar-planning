import z3

def schedule_meeting():
    solver = z3.Solver()
    t = z3.Int('t')
    
    # Work hours constraint: 9:00 to 17:00 (540 to 990 minutes)
    solver.add(t >= 540)  # 9:00 AM
    solver.add(t + 30 <= 990)  # Meeting ends by 5:00 PM
    
    # Roger's preference: No meetings before 12:30 PM (750 minutes)
    solver.add(t >= 750)  # Meeting starts at or after 12:30 PM
    
    # Busy intervals in minutes (start, end)
    busy_intervals = [
        # Cheryl's busy times
        (540, 570),  # 9:00-9:30
        (600, 690),  # 10:00-11:30
        (750, 810),  # 12:30-1:30
        (840, 1020), # 2:00-5:00
        # Virginia's busy times
        (570, 690),  # 9:30-11:30
        (720, 750),  # 12:00-12:30
        (780, 810),  # 1:00-1:30
        (870, 930),  # 2:30-3:30
        (960, 1020), # 4:00-5:00
        # Angela's busy times
        (570, 600),  # 9:30-10:00
        (630, 690),  # 10:30-11:30
        (720, 750),  # 12:00-12:30
        (780, 810),  # 1:00-1:30
        (840, 990),  # 2:00-4:30
        # Kathleen's busy times
        (870, 930),  # 2:30-3:30
        # Carolyn's busy times
        (720, 750),  # 12:00-12:30
        (780, 810)   # 1:00-1:30
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