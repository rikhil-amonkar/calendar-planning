from z3 import Int, Solver, Or, sat

def main():
    s = Int('s')
    solver = Solver()
    
    # Meeting must start between 0 (9:00) and 390 (15:30) to end by 16:00 (420 minutes)
    solver.add(s >= 0)
    solver.add(s <= 390)
    
    # Busy intervals in minutes (half-open: [start, end))
    busy_intervals = [
        (0, 90),      # Juan: 9:00-10:30
        (390, 420),   # Juan: 15:30-16:00
        (120, 150),   # Marilyn: 11:00-11:30
        (210, 240),   # Marilyn: 12:30-13:00
        (0, 90),      # Ronald: 9:00-10:30
        (180, 210),   # Ronald: 12:00-12:30
        (240, 270),   # Ronald: 13:00-13:30
        (300, 450)    # Ronald: 14:00-16:30
    ]
    
    # Add constraints to avoid busy intervals
    for (b1, b2) in busy_intervals:
        solver.add(Or(s + 30 <= b1, s >= b2))
    
    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        start_minutes = model[s].as_long()
        # Convert minutes to HH:MM format
        hours = 9 + start_minutes // 60
        minutes = start_minutes % 60
        start_time = f"{hours}:{minutes:02d}"
        end_minutes = start_minutes + 30
        end_hours = 9 + end_minutes // 60
        end_minutes = end_minutes % 60
        end_time = f"{end_hours}:{end_minutes:02d}"
        print(f"Monday {start_time} to {end_time}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()