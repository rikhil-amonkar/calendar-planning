from z3 import Solver, Int, Or, sat

def main():
    # Initialize solver
    s = Solver()
    
    # Define start time in minutes from 9:00
    start = Int('start')
    
    # Work hours constraint: meeting must be within 9:00 to 17:00 (0 to 480 minutes)
    s.add(start >= 0)
    s.add(start + 30 <= 480)  # Meeting ends by 17:00 (480 minutes)
    
    # Jose's constraint: meeting must end by 15:30 (390 minutes)
    s.add(start + 30 <= 390)  # start <= 360
    
    # Busy intervals in minutes from 9:00 (each interval is [start, end))
    busy_intervals = {
        'Jose': [(120, 150), (210, 240)],
        'Keith': [(300, 330), (360, 390)],
        'Logan': [(0, 60), (180, 210), (360, 390)],
        'Megan': [(0, 90), (120, 180), (240, 270), (330, 450)],
        'Gary': [(0, 30), (60, 90), (150, 240), (270, 300), (330, 450)],
        'Bobby': [(120, 150), (180, 210), (240, 420)]
    }
    
    # Add constraints for each participant's busy intervals
    for participant, intervals in busy_intervals.items():
        for (A, B) in intervals:
            s.add(Or(start + 30 <= A, start >= B))
    
    # Check if a solution exists
    if s.check() == sat:
        model = s.model()
        start_minutes = model[start].as_long()
        
        # Convert minutes back to time
        hours = 9 + start_minutes // 60
        minutes = start_minutes % 60
        end_minutes = start_minutes + 30
        end_hours = 9 + end_minutes // 60
        end_minutes = end_minutes % 60
        
        # Format the time as HH:MM
        start_time = f"{hours}:{minutes:02d}"
        end_time = f"{end_hours}:{end_minutes:02d}"
        
        # Output the solution
        print(f"Monday, {start_time} to {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()