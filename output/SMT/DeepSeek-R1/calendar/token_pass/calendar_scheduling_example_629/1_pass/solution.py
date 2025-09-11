from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Define day variable: 0 for Monday, 1 for Tuesday
    day = Int('day')
    s.add(Or(day == 0, day == 1))
    
    # Define start time in minutes from 9:00 (0 = 9:00, 480 = 17:00)
    start = Int('start')
    s.add(start >= 0)
    s.add(start <= 450)  # 480 - 30 minutes meeting duration
    
    # Margaret's constraints: does not want Monday
    s.add(day != 0)
    
    # Margaret's Tuesday before 14:30 constraint: start must be >= 330 (14:30)
    s.add(If(day == 1, start >= 330, True))
    
    # Margaret's busy times on Tuesday (in minutes from 9:00)
    margaret_tue_busy = [(180, 210)]  # 12:00-12:30
    
    # Alexis's busy times on Tuesday (in minutes from 9:00)
    alexis_tue_busy = [
        (0, 30),    # 9:00-9:30
        (60, 90),   # 10:00-10:30
        (300, 450)  # 14:00-16:30
    ]
    
    # Ensure meeting does not overlap with busy times for Tuesday
    for busy_start, busy_end in margaret_tue_busy:
        s.add(If(day == 1, 
                 Or(start + 30 <= busy_start, start >= busy_end), 
                 True))
    
    for busy_start, busy_end in alexis_tue_busy:
        s.add(If(day == 1, 
                 Or(start + 30 <= busy_start, start >= busy_end), 
                 True))
    
    # Check for solution
    if s.check() == sat:
        m = s.model()
        d = m[day].as_long()
        s_val = m[start].as_long()
        
        # Convert start time to HH:MM format
        start_hour = 9 + s_val // 60
        start_minute = s_val % 60
        end_time = s_val + 30
        end_hour = 9 + end_time // 60
        end_minute = end_time % 60
        
        # Format time strings
        start_str = f"{start_hour:02d}:{start_minute:02d}"
        end_str = f"{end_hour:02d}:{end_minute:02d}"
        day_str = "Tuesday" if d == 1 else "Monday"
        
        print(f"{day_str} {start_str}:{end_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()