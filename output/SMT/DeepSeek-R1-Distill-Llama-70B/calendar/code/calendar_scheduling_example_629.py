import z3

def schedule_meeting():
    solver = z3.Solver()
    t = z3.Int('t')
    
    # Work hours constraint: 9:00 to 17:00 (540 to 1020 minutes)
    solver.add(t >= 540)  # 9:00 AM
    solver.add(t + 30 <= 1020)  # Meeting ends by 5:00 PM
    
    # Margaret's preference: No meetings on Monday
    # This is handled by only considering Tuesday
    # Margaret's busy times on Tuesday
    busy_intervals = [
        (720, 750),  # 12:00-12:30
        # Alexis's busy times on Tuesday
        (540, 570),  # 9:00-9:30
        (600, 630),  # 10:00-10:30
        (840, 990)   # 14:00-16:30
    ]
    
    # Additional constraint: Meeting must start after 14:30 (870 minutes)
    solver.add(t >= 870)
    
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