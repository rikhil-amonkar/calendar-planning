from z3 import *

def solve_scheduling():
    # Create the solver
    s = Solver()
    
    # Define variables
    day = Int('day')  # 0 for Monday, 1 for Tuesday
    start_time = Int('start_time')  # in minutes from 9:00 (0 = 9:00, 30 = 9:30, etc.)
    end_time = Int('end_time')
    
    # Constraints for day
    s.add(Or(day == 0, day == 1))  # Monday or Tuesday
    
    # Working hours: 9:00 to 17:00 (8 hours = 480 minutes)
    # Meeting duration is 30 minutes
    s.add(start_time >= 0)
    s.add(end_time == start_time + 30)
    s.add(end_time <= 480)  # 17:00 is 8 hours after 9:00 (480 minutes)
    
    # Margaret's constraints
    # Margaret does not want to meet on Monday (day == 0)
    s.add(day != 0)
    
    # Margaret's blocked times on Tuesday: 12:00 to 12:30
    # Convert to minutes from 9:00: 12:00 is 180, 12:30 is 210
    margaret_tuesday_blocked_start = 180
    margaret_tuesday_blocked_end = 210
    s.add(Or(
        end_time <= margaret_tuesday_blocked_start,
        start_time >= margaret_tuesday_blocked_end
    ))
    
    # Margaret prefers Tuesday after 14:30 (14:30 is 330 minutes from 9:00)
    s.add(start_time >= 330)
    
    # Alexis's constraints on Tuesday
    # Alexis's blocked times on Tuesday:
    # 9:00-9:30 (0-30), 10:00-10:30 (60-90), 14:00-16:30 (300-450)
    alexis_tuesday_blocks = [(0, 30), (60, 90), (300, 450)]
    for block_start, block_end in alexis_tuesday_blocks:
        s.add(Or(
            end_time <= block_start,
            start_time >= block_end
        ))
    
    # Check if there's a solution
    if s.check() == sat:
        m = s.model()
        day_val = m[day].as_long()
        start_min = m[start_time].as_long()
        
        # Convert day to string
        day_str = "Monday" if day_val == 0 else "Tuesday"
        
        # Convert start_min to HH:MM
        start_hour = 9 + start_min // 60
        start_min = start_min % 60
        start_time_str = f"{start_hour:02d}:{start_min:02d}"
        
        # Calculate end time
        end_min = start_min + 30
        end_hour = start_hour + end_min // 60
        end_min = end_min % 60
        end_time_str = f"{end_hour:02d}:{end_min:02d}"
        
        # Print the solution
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_scheduling()