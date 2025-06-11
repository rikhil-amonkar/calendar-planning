from z3 import *

def main():
    # Create the start time variable (in minutes from 9:00)
    start = Int('start')
    s = Solver()
    
    # Global constraints: within 9:00 to 17:00 (480 minutes from 9:00)
    s.add(start >= 0)
    s.add(start + 60 <= 480)
    
    # Busy intervals for Julie, Sean, and Lori (each as (start_minute, end_minute))
    busy_intervals = [
        # Julie's busy intervals
        (0, 30), (120, 150), (180, 210), (270, 300), (420, 480),
        # Sean's busy intervals
        (0, 30), (240, 270), (360, 390), (420, 450),
        # Lori's busy intervals
        (60, 90), (120, 240), (390, 480)
    ]
    
    # Add constraints for each busy interval
    for (s_busy, e_busy) in busy_intervals:
        s.add(Or(start + 60 <= s_busy, start >= e_busy))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        start_val = m[start].as_long()
        
        # Convert start time to HH:MM
        total_minutes = start_val
        hours = 9 + total_minutes // 60
        minutes = total_minutes % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        
        # Calculate end time (start time + 60 minutes)
        end_total_minutes = total_minutes + 60
        end_hours = 9 + end_total_minutes // 60
        end_minutes = end_total_minutes % 60
        end_time = f"{end_hours:02d}:{end_minutes:02d}"
        
        print(f"Monday {start_time} to {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()