import z3

def schedule_meeting():
    solver = z3.Solver()
    t = z3.Int('t')
    
    # Work hours constraint: 9:00 to 17:00 (540 to 1020 minutes)
    solver.add(t >= 540)  # 9:00 AM
    solver.add(t + 30 <= 1020)  # Meeting ends by 5:00 PM
    
    # Ryan's constraints: Cannot meet on Wednesday
    # This is handled by only considering Monday and Tuesday
    # Ryan's busy times on Monday
    busy_intervals = [
        # Ryan's busy times on Monday
        (570, 600),  # 9:30-10:00
        (660, 720),  # 11:00-12:00
        (780, 810),  # 13:00-13:30
        (930, 960),  # 15:30-16:00
        # Adam's busy times on Monday
        (540, 630),  # 9:00-10:30
        (660, 810),  # 11:00-13:30
        (840, 960),  # 14:00-16:00
        (990, 1020)  # 16:30-17:00
    ]
    
    # Adam's preference: No meetings on Monday before 14:30 (870 minutes)
    solver.add(t >= 870)  # Meeting starts at or after 14:30
    
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