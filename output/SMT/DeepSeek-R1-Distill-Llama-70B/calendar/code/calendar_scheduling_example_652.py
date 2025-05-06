import z3

def schedule_meeting():
    solver = z3.Solver()
    t = z3.Int('t')
    
    # Work hours constraint: 9:00 to 17:00 (540 to 1020 minutes)
    solver.add(t >= 540)  # 9:00 AM
    solver.add(t + 30 <= 1020)  # Meeting ends by 5:00 PM
    
    # Lawrence's constraint: Meeting must end by 16:30 (990 minutes)
    solver.add(t + 30 <= 990)  # Meeting ends by 16:30
    
    # Busy intervals in minutes (start, end)
    busy_intervals = [
        # Jesse's busy times on Tuesday
        (540, 570),  # 9:00-9:30
        (780, 810),  # 13:00-13:30
        (840, 900),  # 14:00-15:00
        # Lawrence's busy times on Tuesday
        (570, 630),  # 9:30-10:30
        (690, 750),  # 11:30-12:30
        (780, 810),  # 13:00-13:30
        (870, 900),  # 14:30-15:00
        (930, 990)   # 15:30-16:30
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