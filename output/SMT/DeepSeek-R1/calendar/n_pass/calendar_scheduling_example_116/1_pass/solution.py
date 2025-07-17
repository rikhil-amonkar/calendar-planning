from z3 import *

def main():
    s = Solver()
    
    # Start time in minutes from 9:00 (0 minutes = 9:00)
    start = Int('start')
    
    # Meeting must be within 9:00 to 17:00 (0 to 480 minutes), duration 30 minutes -> start between 0 and 450 inclusive.
    s.add(start >= 0)
    s.add(start <= 450)
    
    # Adam's busy interval: 14:00 to 15:00 (300 to 360 minutes)
    adam_busy = [(300, 360)]
    for (b_start, b_end) in adam_busy:
        s.add(Or(start + 30 <= b_start, start >= b_end))
    
    # John's busy intervals: 
    # 13:00-13:30 (240-270), 14:00-14:30 (300-330), 15:30-16:00 (390-420), 16:30-17:00 (450-480)
    john_busy = [(240, 270), (300, 330), (390, 420), (450, 480)]
    for (b_start, b_end) in john_busy:
        s.add(Or(start + 30 <= b_start, start >= b_end))
    
    # Stephanie's busy intervals: 
    # 9:30-10:00 (30-60), 10:30-11:00 (90-120), 11:30-16:00 (150-420), 16:30-17:00 (450-480)
    stephanie_busy = [(30, 60), (90, 120), (150, 420), (450, 480)]
    for (b_start, b_end) in stephanie_busy:
        s.add(Or(start + 30 <= b_start, start >= b_end))
    
    # Anna's busy intervals: 
    # 9:30-10:00 (30-60), 12:00-12:30 (180-210), 13:00-15:30 (240-390), 16:30-17:00 (450-480)
    anna_busy = [(30, 60), (180, 210), (240, 390), (450, 480)]
    for (b_start, b_end) in anna_busy:
        s.add(Or(start + 30 <= b_start, start >= b_end))
    
    # Anna's preference: not before 14:30 (330 minutes)
    s.add(start >= 330)
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        start_val = m[start].as_long()
        
        # Convert start time back to HH:MM format
        total_minutes_from_midnight = 9 * 60 + start_val
        hours = total_minutes_from_midnight // 60
        minutes = total_minutes_from_midnight % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        
        # Calculate end time (start time + 30 minutes)
        end_minutes = total_minutes_from_midnight + 30
        end_hours = end_minutes // 60
        end_minutes = end_minutes % 60
        end_time = f"{end_hours:02d}:{end_minutes:02d}"
        
        # Output the solution
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()