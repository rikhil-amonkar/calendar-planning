from z3 import *

def main():
    s = Solver()
    
    day = Int('day')
    start_minutes = Int('start_minutes')  # Minutes from 9:00

    # Day constraints: only Tuesday (1) is allowed
    s.add(day == 1)  # Tuesday
    
    # Start time constraints: must be between 180 (12:00) and 450 (16:30) minutes from 9:00
    s.add(start_minutes >= 180)
    s.add(start_minutes <= 450)  # 450 minutes = 16:30, so meeting ends at 17:00
    
    # Daniel's busy intervals on Tuesday (each tuple is (start_minute, end_minute) from 9:00)
    daniel_busy_tue = [
        (120, 180),   # 11:00-12:00
        (240, 270),   # 13:00-13:30
        (390, 420),   # 15:30-16:00
        (450, 480)    # 16:30-17:00
    ]
    
    # Bradley's busy intervals on Tuesday
    bradley_busy_tue = [
        (90, 120),    # 10:30-11:00
        (180, 240),   # 12:00-13:00
        (270, 300),   # 13:30-14:00
        (390, 450)    # 15:30-16:30
    ]
    
    # Add constraints for Daniel: meeting [start_minutes, start_minutes+30] must not overlap with any busy interval
    for (busy_start, busy_end) in daniel_busy_tue:
        s.add(Or(start_minutes + 30 <= busy_start, start_minutes >= busy_end))
    
    # Add constraints for Bradley
    for (busy_start, busy_end) in bradley_busy_tue:
        s.add(Or(start_minutes + 30 <= busy_start, start_minutes >= busy_end))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        day_val = m[day].as_long()
        start_val = m[start_minutes].as_long()
        
        # Convert start time to HH:MM format
        total_minutes = start_val
        hours = 9 + total_minutes // 60
        minutes = total_minutes % 60
        start_time_str = f"{hours}:{minutes:02d}"
        
        # Calculate end time
        end_total_minutes = total_minutes + 30
        end_hours = 9 + end_total_minutes // 60
        end_minutes = end_total_minutes % 60
        end_time_str = f"{end_hours}:{end_minutes:02d}"
        
        # Map day value to string
        days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
        day_str = days[day_val]
        
        # Output the solution
        print(f"Day: {day_str}, Start: {start_time_str}, End: {end_time_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()