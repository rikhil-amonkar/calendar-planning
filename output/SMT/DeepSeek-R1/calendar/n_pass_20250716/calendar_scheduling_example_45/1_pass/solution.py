from z3 import *

def main():
    # Initialize solver with optimization
    opt = Optimize()
    
    # Start time in minutes from 9:00
    S = Int('S')
    
    # Work hours: 9:00 (0 min) to 17:00 (480 min)
    opt.add(S >= 0)
    opt.add(S + 30 <= 480)
    
    # Samuel's busy intervals (each as [start, end) in minutes)
    busy_intervals = [
        (0, 90),
        (150, 180),
        (240, 270),
        (300, 420),
        (450, 480)
    ]
    
    # Add constraints to avoid each busy interval
    for a, b in busy_intervals:
        opt.add(Or(S + 30 <= a, S >= b))
    
    # Minimize the start time S
    opt.minimize(S)
    
    # Check for a solution
    if opt.check() == sat:
        m = opt.model()
        start_minutes = m[S].as_long()
        
        # Convert start_minutes to time string
        hours = start_minutes // 60
        minutes = start_minutes % 60
        start_time = f"{9 + hours}:{minutes:02d}"
        
        # Calculate end time
        end_minutes = start_minutes + 30
        hours_end = end_minutes // 60
        minutes_end = end_minutes % 60
        end_time = f"{9 + hours_end}:{minutes_end:02d}"
        
        # Output the meeting details
        print("Monday")
        print(start_time)
        print(end_time)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()