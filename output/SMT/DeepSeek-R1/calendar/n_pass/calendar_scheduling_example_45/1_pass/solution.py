from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Define start time variable in minutes (from 9:00)
    S = Int('S')
    
    # Duration of the meeting in minutes
    duration = 30
    
    # Total available time: 9:00 (0 min) to 17:00 (480 min)
    max_time = 480
    s.add(S >= 0)
    s.add(S <= max_time - duration)
    
    # Samuel's busy intervals in minutes (relative to 9:00)
    busy_intervals = [
        (0, 90),
        (150, 180),
        (240, 270),
        (300, 420),
        (450, 480)
    ]
    
    # Add constraints: the meeting [S, S+duration] must not overlap any busy interval
    for (start_busy, end_busy) in busy_intervals:
        s.add(Or(S + duration <= start_busy, S >= end_busy))
    
    # Find the earliest time (minimal S)
    s.push()
    s.check()
    model = s.model()
    start_minutes = model.eval(S).as_long()
    
    # Convert start_minutes back to time string
    hours = 9 + start_minutes // 60
    minutes = start_minutes % 60
    start_time = f"{hours:02d}:{minutes:02d}"
    
    # Calculate end time
    end_minutes = start_minutes + duration
    end_hours = 9 + end_minutes // 60
    end_minutes_remainder = end_minutes % 60
    end_time = f"{end_hours:02d}:{end_minutes_remainder:02d}"
    
    # Output the solution
    print("SOLUTION:")
    print("Day: Monday")
    print(f"Start Time: {start_time}")
    print(f"End Time: {end_time}")

if __name__ == "__main__":
    main()