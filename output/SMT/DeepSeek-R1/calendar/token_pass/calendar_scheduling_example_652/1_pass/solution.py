from z3 import *

def main():
    # Create solver
    s = Solver()
    
    # Define variables: day (0=Monday, 1=Tuesday) and start time in minutes from 9:00
    day = Int('day')
    start_time = Int('start_time')
    
    # Meeting duration in minutes
    duration = 30
    
    # Convert work hours to minutes: 9:00 to 17:00 is 480 minutes (8 hours)
    total_minutes = 480
    
    # Constraint: day must be either 0 or 1
    s.add(Or(day == 0, day == 1))
    
    # General constraint: start_time must be non-negative and allow the meeting to end by 17:00
    s.add(start_time >= 0)
    s.add(start_time <= total_minutes - duration)
    
    # Lawrence cannot meet on Tuesday after 16:30, which is 450 minutes from 9:00 (16:30 - 9:00 = 7h30m = 450m)
    # So the meeting must end by 450 minutes on Tuesday, meaning start_time + duration <= 450
    s.add(If(day == 1, start_time + duration <= 450, True))
    
    # Jesse's busy intervals (day, start_minutes, end_minutes)
    jesse_busy = [
        (0, 270, 300),  # Monday 13:30-14:00
        (0, 330, 360),  # Monday 14:30-15:00
        (1, 0, 30),     # Tuesday 9:00-9:30
        (1, 240, 270),  # Tuesday 13:00-13:30
        (1, 300, 360)   # Tuesday 14:00-15:00
    ]
    
    # Lawrence's busy intervals
    lawrence_busy = [
        (0, 0, 480),    # Monday all day
        (1, 30, 90),    # Tuesday 9:30-10:30
        (1, 150, 210),  # Tuesday 11:30-12:30
        (1, 240, 270),  # Tuesday 13:00-13:30
        (1, 330, 360),  # Tuesday 14:30-15:00
        (1, 390, 450)   # Tuesday 15:30-16:30
    ]
    
    # For Jesse: meeting must not overlap with any busy interval on the chosen day
    for d, busystart, busyend in jesse_busy:
        s.add(If(day == d, Not(And(start_time < busyend, start_time + duration > busystart)), True))
    
    # For Lawrence: meeting must not overlap with any busy interval on the chosen day
    for d, busystart, busyend in lawrence_busy:
        s.add(If(day == d, Not(And(start_time < busyend, start_time + duration > busystart)), True))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        d_val = m[day].as_long()
        start_val = m[start_time].as_long()
        
        # Calculate start time in hours and minutes
        start_hour = 9 + start_val // 60
        start_minute = start_val % 60
        end_val = start_val + duration
        end_hour = 9 + end_val // 60
        end_minute = end_val % 60
        
        # Format the time strings
        start_str = f"{start_hour:02d}:{start_minute:02d}"
        end_str = f"{end_hour:02d}:{end_minute:02d}"
        day_str = "Monday" if d_val == 0 else "Tuesday"
        
        print(f"{day_str} {start_str}:{end_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()