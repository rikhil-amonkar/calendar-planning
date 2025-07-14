from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()
    
    # Convert times to minutes since 9:00 (540 minutes from midnight)
    # Meeting duration is 30 minutes
    duration = 30
    
    # Define the start time variable (in minutes from 9:00, so 0 is 9:00)
    start_time = Int('start_time')
    
    # Total working hours: 9:00-17:00 is 480 minutes (8 hours)
    max_time = 8 * 60  # 17:00 is 8*60 minutes after 9:00 (i.e., 540 + 480 = 1020 minutes or 17:00)
    
    # Meeting must start >= 0 (9:00) and end <= 480 (17:00 is 480 minutes after 9:00)
    s.add(start_time >= 0)
    s.add(start_time + duration <= max_time)
    
    # Evelyn's constraints: no meetings after 13:00 (13:00 is 4*60=240 minutes after 9:00)
    # So meeting must end by 13:00 (i.e., start_time + 30 <= 240)
    s.add(start_time + duration <= 4 * 60)  # 13:00 is 4 hours after 9:00 (240 minutes)
    
    # Randy's constraints:
    # Randy's blocked times in minutes from 9:00:
    # 9:00-10:30: 0 to 90 minutes
    # 11:00-15:30: 120 to 390 minutes
    # 16:00-17:00: 420 to 480 minutes
    # So available times are 90-120 (10:30-11:00) and 390-420 (15:30-16:00)
    
    # The meeting must fit entirely within one of Randy's available slots.
    # So either:
    # (start_time >= 90 and start_time + duration <= 120) OR
    # (start_time >= 390 and start_time + duration <= 420)
    s.add(Or(
        And(start_time >= 90, start_time + duration <= 120),
        And(start_time >= 390, start_time + duration <= 420)
    ))
    
    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        start_minutes = m[start_time].as_long()
        
        # Convert start_minutes back to HH:MM format
        total_minutes_from_midnight = 540 + start_minutes  # 9:00 is 540 minutes
        hours = total_minutes_from_midnight // 60
        minutes = total_minutes_from_midnight % 60
        start_time_str = f"{hours:02d}:{minutes:02d}"
        
        end_minutes = start_minutes + duration
        total_end_minutes_from_midnight = 540 + end_minutes
        end_hours = total_end_minutes_from_midnight // 60
        end_minutes_part = total_end_minutes_from_midnight % 60
        end_time_str = f"{end_hours:02d}:{end_minutes_part:02d}"
        
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_scheduling()