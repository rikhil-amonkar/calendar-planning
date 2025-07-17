from z3 import *

def main():
    # Create solver
    s = Solver()
    
    # Define variables
    day = Int('day')  # 0: Monday, 1: Tuesday, 2: Wednesday
    start_minutes = Int('start_minutes')  # minutes from 9:00, range [0, 450] (since meeting is 30 min and must end by 17:00)
    
    # Basic constraints for day and start time
    s.add(day >= 0, day <= 2)
    s.add(start_minutes >= 0, start_minutes <= 450)  # 450 = 480 - 30 (30 minutes meeting)
    
    # Monday constraints (day 0)
    ruth_monday_busy = [(0, 60), (90, 180), (210, 330), (360, 420), (450, 480)]
    monday_constraint = And(
        # Ruth's busy intervals: meeting must not overlap
        *[Or(start_minutes + 30 <= a, start_minutes >= b) for a, b in ruth_monday_busy],
        # Tyler's preference: avoid before 16:00 (420 minutes from 9:00)
        start_minutes >= 420
    )
    
    # Tuesday constraints (day 1) - Ruth is busy all day
    ruth_tuesday_busy = [(0, 480)]
    tyler_tuesday_busy = [(0, 30), (330, 360)]  # Tyler's busy times on Tuesday
    tuesday_constraint = And(
        *[Or(start_minutes + 30 <= a, start_minutes >= b) for a, b in ruth_tuesday_busy],
        *[Or(start_minutes + 30 <= a, start_minutes >= b) for a, b in tyler_tuesday_busy]
    )
    
    # Wednesday constraints (day 2) - Ruth is busy all day
    ruth_wednesday_busy = [(0, 480)]
    tyler_wednesday_busy = [(90, 120), (210, 240), (270, 300), (450, 480)]  # Tyler's busy times on Wednesday
    wednesday_constraint = And(
        *[Or(start_minutes + 30 <= a, start_minutes >= b) for a, b in ruth_wednesday_busy],
        *[Or(start_minutes + 30 <= a, start_minutes >= b) for a, b in tyler_wednesday_busy]
    )
    
    # Conditional constraints based on the day
    s.add(If(day == 0, monday_constraint, 
              If(day == 1, tuesday_constraint, wednesday_constraint)))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        day_val = m[day].as_long()
        start_minutes_val = m[start_minutes].as_long()
        
        # Convert day value to string
        days = ["Monday", "Tuesday", "Wednesday"]
        day_str = days[day_val]
        
        # Calculate start time (HH:MM)
        total_minutes = start_minutes_val
        hours = total_minutes // 60
        minutes = total_minutes % 60
        start_hour = 9 + hours
        start_time = f"{start_hour:02d}:{minutes:02d}"
        
        # Calculate end time (start time + 30 minutes)
        end_minutes_val = start_minutes_val + 30
        end_hours = end_minutes_val // 60
        end_minutes = end_minutes_val % 60
        end_hour = 9 + end_hours
        end_time = f"{end_hour:02d}:{end_minutes:02d}"
        
        # Output the solution
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()