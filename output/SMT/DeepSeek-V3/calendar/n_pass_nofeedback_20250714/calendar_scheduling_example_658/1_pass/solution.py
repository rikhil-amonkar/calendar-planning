from z3 import *

def solve_meeting_schedule():
    # Create the solver
    solver = Solver()
    
    # Define variables
    day = Int('day')  # 0 for Monday, 1 for Tuesday
    start_time = Int('start_time')  # in minutes from 9:00 (e.g., 0 is 9:00, 30 is 9:30)
    end_time = Int('end_time')
    
    # Constraints for day: 0 (Monday) or 1 (Tuesday)
    solver.add(Or(day == 0, day == 1))
    
    # Meeting duration is 30 minutes
    solver.add(end_time == start_time + 30)
    
    # Meeting must be within work hours (9:00-17:00, so 0 to 480 minutes)
    solver.add(start_time >= 0)
    solver.add(end_time <= 480)  # 8 hours * 60 = 480 minutes
    
    # Shirley's constraints
    # Monday blocked: 10:30-11:00 (90-120), 12:00-12:30 (180-210), 16:00-16:30 (420-450)
    # Tuesday blocked: 9:30-10:00 (30-60)
    # Shirley's preference: not meet on Tuesday after 10:30 (start_time + 30 <= 90 if day is Tuesday)
    shirley_monday_blocked = Or(
        And(day == 0, start_time >= 90, start_time < 120),   # 10:30-11:00
        And(day == 0, start_time >= 180, start_time < 210),   # 12:00-12:30
        And(day == 0, start_time >= 420, start_time < 450)    # 16:00-16:30
    )
    shirley_tuesday_blocked = And(day == 1, start_time >= 30, start_time < 60)  # 9:30-10:00
    solver.add(Not(shirley_monday_blocked))
    solver.add(Not(shirley_tuesday_blocked))
    
    # Shirley's preference: not meet on Tuesday after 10:30 (i.e., start_time +30 <= 90)
    solver.add(Implies(day == 1, start_time + 30 <= 90))
    
    # Albert's constraints
    # Monday: busy all day (9:00-17:00), so no meeting possible on Monday
    # Tuesday blocked: 9:30-11:00 (30-120), 11:30-12:30 (150-210), 13:00-16:00 (240-420), 16:30-17:00 (450-480)
    albert_monday_blocked = day == 0
    albert_tuesday_blocked = Or(
        And(day == 1, start_time >= 30, start_time < 120),   # 9:30-11:00
        And(day == 1, start_time >= 150, start_time < 210),   # 11:30-12:30
        And(day == 1, start_time >= 240, start_time < 420),   # 13:00-16:00
        And(day == 1, start_time >= 450, start_time < 480)    # 16:30-17:00
    )
    solver.add(Not(albert_monday_blocked))
    solver.add(Not(albert_tuesday_blocked))
    
    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        day_val = model[day].as_long()
        start_val = model[start_time].as_long()
        end_val = model[end_time].as_long()
        
        # Convert day to string
        day_str = "Monday" if day_val == 0 else "Tuesday"
        
        # Convert start and end times to HH:MM format
        start_hh = 9 + start_val // 60
        start_mm = start_val % 60
        end_hh = 9 + end_val // 60
        end_mm = end_val % 60
        
        # Format as two-digit strings
        start_time_str = f"{start_hh:02d}:{start_mm:02d}"
        end_time_str = f"{end_hh:02d}:{end_mm:02d}"
        
        # Print the solution
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_meeting_schedule()