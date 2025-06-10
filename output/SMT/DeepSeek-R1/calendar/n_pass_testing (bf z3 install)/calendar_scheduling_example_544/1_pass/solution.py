from z3 import *

def main():
    # Create solver
    s = Solver()
    
    # Start time in minutes from 9:00
    start = Int('start')
    
    # Constraints: start must be between 0 and 90 (inclusive) because meeting must end by 11:00 (120 minutes from 9:00)
    s.add(start >= 0)
    s.add(start + 30 <= 120)  # meeting ends by 11:00 (120 minutes from 9:00)
    
    # Albert's busy times in minutes from 9:00
    busy_intervals = [
        (0, 60),   # 9:00 to 10:00
        (90, 180)   # 10:30 to 12:00
    ]
    
    # Ensure the meeting does not overlap with any busy interval
    for (busy_start, busy_end) in busy_intervals:
        s.add(Or(start + 30 <= busy_start, start >= busy_end))
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        start_min = model[start].as_long()
        
        # Convert start_min to time string
        hours = start_min // 60
        minutes = start_min % 60
        start_time = f"{9 + hours}:{minutes:02d}"
        
        # Calculate end time
        end_min = start_min + 30
        end_hours = end_min // 60
        end_minutes = end_min % 60
        end_time = f"{9 + end_hours}:{end_minutes:02d}"
        
        print(f"Monday, {start_time}, {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()