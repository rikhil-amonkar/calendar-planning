from z3 import *

def main():
    # Initialize variables
    day = Int('day')
    start = Int('start')
    
    s = Solver()
    
    # Day constraint: 0=Monday, 1=Tuesday, 2=Wednesday
    s.add(day >= 0, day <= 2)
    
    # Start time constraint: meeting must be within 9:00 to 16:00 (start time) to end by 17:00
    s.add(start >= 0, start <= 420)
    
    # Blocked intervals for Martha: (day, start_minute, end_minute)
    martha_intervals = [
        (0, 420, 480),   # Monday: 16:00-17:00 (420 mins = 16:00, 480 mins = 17:00)
        (1, 360, 390),   # Tuesday: 15:00-15:30 (360 mins = 15:00, 390 mins = 15:30)
        (2, 60, 120),    # Wednesday: 10:00-11:00 (60 mins = 10:00, 120 mins = 11:00)
        (2, 300, 330)    # Wednesday: 14:00-14:30 (300 mins = 14:00, 330 mins = 14:30)
    ]
    
    # Blocked intervals for Beverly
    beverly_intervals = [
        (0, 0, 270),     # Monday: 9:00-13:30 (0 mins = 9:00, 270 mins = 13:30)
        (0, 300, 480),   # Monday: 14:00-17:00 (300 mins = 14:00, 480 mins = 17:00)
        (1, 0, 480),     # Tuesday: 9:00-17:00 (entire day)
        (2, 30, 390),    # Wednesday: 9:30-15:30 (30 mins = 9:30, 390 mins = 15:30)
        (2, 450, 480)    # Wednesday: 16:30-17:00 (450 mins = 16:30, 480 mins = 17:00)
    ]
    
    # Add constraints for Martha's blocked intervals
    for d, b_start, b_end in martha_intervals:
        # If meeting is on day 'd', ensure it doesn't overlap with blocked interval
        s.add(If(day == d, Or((start + 60) <= b_start, start >= b_end), True))
    
    # Add constraints for Beverly's blocked intervals
    for d, b_start, b_end in beverly_intervals:
        s.add(If(day == d, Or((start + 60) <= b_start, start >= b_end), True))
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        d_val = model[day].as_long()
        start_minutes = model[start].as_long()
        
        # Convert start_minutes to time string
        hours = 9 + start_minutes // 60
        minutes = start_minutes % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        
        # Calculate end time (start + 60 minutes)
        end_minutes = start_minutes + 60
        end_hours = 9 + end_minutes // 60
        end_minutes = end_minutes % 60
        end_time = f"{end_hours:02d}:{end_minutes:02d}"
        
        # Map day integer to day name
        days = ["Monday", "Tuesday", "Wednesday"]
        day_name = days[d_val]
        
        print(f"Meeting scheduled on {day_name} from {start_time} to {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()