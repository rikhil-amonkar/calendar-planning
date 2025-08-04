from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()
    
    # Meeting duration is 30 minutes
    meeting_duration = 30
    
    # Work hours are from 9:00 (540 minutes from midnight) to 17:00 (1020 minutes)
    # Convert all times to minutes since 9:00 (so 9:00 is 0, 10:00 is 60, etc.)
    day_start = 9 * 60  # 9:00 in minutes since midnight
    day_end = 17 * 60   # 17:00 in minutes since midnight
    
    # The meeting start time (in minutes since 9:00)
    meeting_start = Int('meeting_start')
    
    # Constraints: meeting_start must be >= 0 (9:00) and <= day_end - meeting_duration (16:30)
    s.add(meeting_start >= 0)
    s.add(meeting_start <= (day_end - day_start) - meeting_duration)
    
    # Each participant's blocked times in minutes since 9:00
    # Ronald is free all day
    ronald_blocked = []
    
    # Stephen's blocked times: 10:00-10:30 (60-90), 12:00-12:30 (180-210)
    stephen_blocked = [(60, 90), (180, 210)]
    
    # Brittany's blocked times: 11:00-11:30 (120-150), 13:30-14:00 (270-300), 15:30-16:00 (390-420), 16:30-17:00 (450-480)
    brittany_blocked = [(120, 150), (270, 300), (390, 420), (450, 480)]
    
    # Dorothy's blocked times: 9:00-9:30 (0-30), 10:00-10:30 (60-90), 11:00-12:30 (120-210), 13:00-15:00 (240-360), 15:30-17:00 (390-480)
    dorothy_blocked = [(0, 30), (60, 90), (120, 210), (240, 360), (390, 480)]
    
    # Rebecca's blocked times: 9:30-10:30 (30-90), 11:00-11:30 (120-150), 12:00-12:30 (180-210), 13:00-17:00 (240-480)
    rebecca_blocked = [(30, 90), (120, 150), (180, 210), (240, 480)]
    
    # Jordan's blocked times: 9:00-9:30 (0-30), 10:00-11:00 (60-120), 11:30-12:00 (150-180), 13:00-15:00 (240-360), 15:30-16:30 (390-450)
    jordan_blocked = [(0, 30), (60, 120), (150, 180), (240, 360), (390, 450)]
    
    # Combine all participants' blocked times
    all_blocked = []
    all_blocked.extend(ronald_blocked)
    all_blocked.extend(stephen_blocked)
    all_blocked.extend(brittany_blocked)
    all_blocked.extend(dorothy_blocked)
    all_blocked.extend(rebecca_blocked)
    all_blocked.extend(jordan_blocked)
    
    # For each blocked interval, add a constraint that the meeting does not overlap
    for (start, end) in all_blocked:
        # The meeting does not overlap if it's entirely before or entirely after the blocked interval
        s.add(Or(
            meeting_start + meeting_duration <= start,
            meeting_start >= end
        ))
    
    # Check if there's a solution
    if s.check() == sat:
        m = s.model()
        start_time_min = m[meeting_start].as_long()
        
        # Calculate the start and end times in HH:MM format
        total_start_min = day_start + start_time_min
        start_hour = total_start_min // 60
        start_minute = total_start_min % 60
        start_time_str = f"{start_hour:02d}:{start_minute:02d}"
        
        total_end_min = total_start_min + meeting_duration
        end_hour = total_end_min // 60
        end_minute = total_end_min % 60
        end_time_str = f"{end_hour:02d}:{end_minute:02d}"
        
        # Print the solution
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_scheduling()