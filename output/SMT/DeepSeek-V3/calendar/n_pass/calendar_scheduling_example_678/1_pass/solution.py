from z3 import *

def solve_scheduling():
    # Create solver instance
    s = Solver()
    
    # Define variables
    day = Int('day')  # 0 for Monday, 1 for Tuesday
    start_time = Int('start_time')  # in minutes from 9:00 (e.g., 0 means 9:00, 60 means 10:00)
    
    # Constants
    meeting_duration = 60  # 1 hour in minutes
    work_start = 0  # 9:00 in minutes from 9:00
    work_end = 480  # 17:00 in minutes from 9:00 (8 hours * 60 minutes)
    
    # Constraints for day and start time
    s.add(Or(day == 0, day == 1))  # Day is either Monday (0) or Tuesday (1)
    s.add(start_time >= work_start)
    s.add(start_time + meeting_duration <= work_end)
    
    # Russell's busy times (in minutes from 9:00)
    russell_busy = [
        (day == 0, And(start_time < 150, start_time + meeting_duration > 90)),  # Monday 10:30-11:00 (90 to 120 minutes)
        (day == 1, And(start_time < 270, start_time + meeting_duration > 240))  # Tuesday 13:00-13:30 (240 to 270 minutes)
    ]
    
    # Alexander's busy times (in minutes from 9:00)
    alexander_busy = [
        (day == 0, Or(
            And(start_time < 150, start_time + meeting_duration > 0),  # Monday 9:00-11:30 (0 to 150)
            And(start_time < 330, start_time + meeting_duration > 180),  # Monday 12:00-14:30 (180 to 330)
            And(start_time < 480, start_time + meeting_duration > 360))  # Monday 15:00-17:00 (360 to 480)
        ),
        (day == 1, Or(
            And(start_time < 60, start_time + meeting_duration > 0),  # Tuesday 9:00-10:00 (0 to 60)
            And(start_time < 240, start_time + meeting_duration > 180),  # Tuesday 13:00-14:00 (240 to 300)
            And(start_time < 390, start_time + meeting_duration > 360),  # Tuesday 15:00-15:30 (360 to 390)
            And(start_time < 450, start_time + meeting_duration > 420))  # Tuesday 16:00-16:30 (420 to 450)
        )
    ]
    
    # Add constraints for not overlapping with busy times
    for (day_cond, busy_cond) in russell_busy:
        s.add(Implies(day_cond, Not(busy_cond)))
    
    for (day_cond, busy_cond) in alexander_busy:
        s.add(Implies(day_cond, Not(busy_cond))))
    
    # Russell's preference: not on Tuesday before 13:30 (240 minutes from 9:00)
    s.add(Implies(day == 1, start_time >= 240))
    
    # Check for solution
    if s.check() == sat:
        model = s.model()
        day_val = model[day].as_long()
        start_val = model[start_time].as_long()
        
        # Convert start time to HH:MM format
        start_hour = 9 + start_val // 60
        start_minute = start_val % 60
        start_time_str = f"{start_hour:02d}:{start_minute:02d}"
        
        # Calculate end time
        end_hour = 9 + (start_val + meeting_duration) // 60
        end_minute = (start_val + meeting_duration) % 60
        end_time_str = f"{end_hour:02d}:{end_minute:02d}"
        
        day_str = "Monday" if day_val == 0 else "Tuesday"
        
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_scheduling()