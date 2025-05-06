import z3

def schedule_meeting():
    solver = z3.Solver()
    t = z3.Int('t')
    
    # Work hours constraint: 9:00 to 17:00 (540 to 1020 minutes)
    solver.add(t >= 540)  # 9:00 AM
    solver.add(t + 30 <= 1020)  # Meeting ends by 5:00 PM
    
    # Helen's preference: Meeting must end by 13:30 (810 minutes)
    solver.add(t + 30 <= 810)  # t <= 780
    
    # Busy intervals in minutes (start, end)
    busy_intervals = [
        # Margaret's busy times
        (540, 600),  # 9:00-10:00
        (630, 660),  # 10:30-11:00
        (690, 720),  # 11:30-12:00
        (780, 810),  # 13:00-13:30
        (900, 930),  # 15:00-15:30
        # Donna's busy times
        (870, 900),  # 14:30-15:00
        (960, 990),  # 16:00-16:30
        # Helen's busy times
        (540, 570),  # 9:00-9:30
        (600, 690),  # 10:00-11:30
        (780, 840),  # 13:00-14:00
        (870, 900),  # 14:30-15:00
        (930, 1020)  # 15:30-17:00
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