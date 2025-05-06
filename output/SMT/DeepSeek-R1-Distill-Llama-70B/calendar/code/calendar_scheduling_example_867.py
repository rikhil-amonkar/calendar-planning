import z3

def schedule_meeting():
    solver = z3.Solver()
    t = z3.Int('t')
    
    # Work hours constraint: 9:00 to 17:00 (540 to 1020 minutes)
    solver.add(t >= 540)  # 9:00 AM
    solver.add(t + 30 <= 1020)  # Meeting ends by 5:00 PM
    
    # Betty's constraints: Not available on Monday, Tuesday, or Thursday before 15:00 (900 minutes)
    solver.add(t >= 900)  # Meeting starts after 15:00
    
    # Scott's constraints: Available on Thursday
    # This is handled by only considering Thursday
    
    # Busy intervals in minutes (start, end)
    busy_intervals = [
        # Betty's busy times on Thursday
        (570, 600),  # 9:30-10:00
        (630, 660),  # 10:30-11:00
        (690, 750),  # 11:30-12:30
        (780, 900),  # 13:00-15:00
        (960, 990),  # 16:00-16:30
        # Scott's busy times on Thursday
        (540, 570),  # 9:00-9:30
        (600, 630),  # 10:00-10:30
        (660, 720),  # 11:00-12:00
        (750, 780),  # 12:30-13:00
        (900, 960),  # 15:00-16:00
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