import z3

def schedule_meeting():
    solver = z3.Solver()
    t = z3.Int('t')
    
    # Work hours constraint: 9:00 to 17:00 (540 to 1020 minutes)
    solver.add(t >= 540)  # 9:00 AM
    solver.add(t + 60 <= 1020)  # Meeting ends by 5:00 PM
    
    # Russell's preference: No meetings before 13:30 (810 minutes)
    solver.add(t >= 810)  # Meeting starts at or after 13:30
    
    # Busy intervals in minutes (start, end)
    busy_intervals = [
        # Russell's busy times on Tuesday
        (780, 810),  # 13:00-13:30
        # Alexander's busy times on Tuesday
        (540, 600),  # 9:00-10:00
        (780, 840),  # 13:00-14:00
        (900, 930),  # 15:00-15:30
        (960, 990)   # 16:00-16:30
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