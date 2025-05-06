import z3

def schedule_meeting():
    solver = z3.Solver()
    t = z3.Int('t')
    
    # Work hours constraint: 9:00 to 17:00 (540 to 1020 minutes)
    solver.add(t >= 540)  # 9:00 AM
    solver.add(t <= 990)  # 4:30 PM (meeting ends by 5:00 PM)
    
    # Julie's preference: No meetings on Thursday before 11:30 AM (690 minutes)
    solver.add(z3.Or(t < 540 + 4 * 60,  # Monday
                      t < 540 + 5 * 60,  # Tuesday
                      t < 540 + 6 * 60,  # Wednesday
                      t >= 690))         # Thursday after 11:30
    
    # Ruth's busy intervals in minutes (start, end)
    busy_intervals = [
        # Monday
        (540, 1020), # 9:00-17:00
        # Tuesday
        (540, 1020), # 9:00-17:00
        # Wednesday
        (540, 1020), # 9:00-17:00
        # Thursday
        (540, 660),  # 9:00-11:00
        (690, 870),  # 11:30-14:30
        (900, 1020)  # 15:00-17:00
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