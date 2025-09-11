from z3 import *

def main():
    # Create solver
    s = Solver()
    
    # Define variables
    day = Int('day')  # 0 for Monday, 1 for Tuesday
    start = Int('start')  # Minutes from 9:00
    
    # Meeting duration in minutes
    duration = 30
    
    # Work hours: 9:00 to 17:00 (480 minutes from 9:00)
    max_time = 480
    
    # Day constraints: Monday (0) or Tuesday (1)
    s.add(day >= 0, day <= 1)
    
    # Time must be within work hours
    s.add(start >= 0, start + duration <= max_time)
    
    # Amanda's busy intervals (minutes from 9:00)
    amanda_busy = [
        (0, 0, 90),    # Monday 9:00-10:30
        (0, 120, 150), # Monday 11:00-11:30
        (0, 210, 240), # Monday 12:30-13:00
        (0, 270, 300), # Monday 13:30-14:00
        (0, 330, 360), # Monday 14:30-15:00
        (1, 0, 30),    # Tuesday 9:00-9:30
        (1, 60, 90),   # Tuesday 10:00-10:30
        (1, 150, 180), # Tuesday 11:30-12:00
        (1, 270, 330), # Tuesday 13:30-14:30
        (1, 390, 420), # Tuesday 15:30-16:00
        (1, 450, 480)  # Tuesday 16:30-17:00
    ]
    
    # Nathan's busy intervals (minutes from 9:00)
    nathan_busy = [
        (0, 60, 90),   # Monday 10:00-10:30
        (0, 120, 150), # Monday 11:00-11:30
        (0, 270, 330), # Monday 13:30-14:30
        (0, 420, 450), # Monday 16:00-16:30
        (1, 0, 90),    # Tuesday 9:00-10:30
        (1, 120, 240), # Tuesday 11:00-13:00
        (1, 270, 300), # Tuesday 13:30-14:00
        (1, 330, 390), # Tuesday 14:30-15:30
        (1, 420, 450)  # Tuesday 16:00-16:30
    ]
    
    # Add constraints for Amanda's busy intervals
    for d, busystart, busyend in amanda_busy:
        # If current day matches, ensure no overlap
        s.add(Implies(day == d, Not(And(start < busyend, start + duration > busystart))))
    
    # Add constraints for Nathan's busy intervals
    for d, busystart, busyend in nathan_busy:
        s.add(Implies(day == d, Not(And(start < busyend, start + duration > busystart))))
    
    # Additional constraints
    # Nathan cannot meet on Monday
    s.add(day != 0)
    # Amanda doesn't want Tuesday after 11:00 (11:00 = 120 minutes from 9:00)
    s.add(Implies(day == 1, start + duration <= 120))
    
    # Check for solution
    if s.check() == sat:
        m = s.model()
        d_val = m[day].as_long()
        start_val = m[start].as_long()
        
        # Calculate start time in HH:MM format
        start_hour = 9 + start_val // 60
        start_minute = start_val % 60
        end_val = start_val + duration
        end_hour = 9 + end_val // 60
        end_minute = end_val % 60
        
        # Format time strings
        start_str = f"{start_hour:02d}:{start_minute:02d}"
        end_str = f"{end_hour:02d}:{end_minute:02d}"
        day_str = "Tuesday" if d_val == 1 else "Monday"
        
        print(f"{day_str}:{start_str}:{end_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()