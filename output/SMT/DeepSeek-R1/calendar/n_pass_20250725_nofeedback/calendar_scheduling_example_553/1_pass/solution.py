from z3 import *

def main():
    # Create an optimizer
    s = Optimize()
    
    # Start time in minutes from 9:00 (0 minutes = 9:00)
    start = Int('start')
    
    # Meeting duration is 30 minutes
    duration = 30
    
    # Total available minutes from 9:00 to 17:00 (8 hours = 480 minutes)
    total_minutes = 480
    s.add(start >= 0)
    s.add(start <= total_minutes - duration)  # Meeting must end by 17:00
    
    # Eric's blocked times in minutes from 9:00
    eric_blocked1_start = (12 - 9) * 60   # 180 minutes (12:00)
    eric_blocked1_end = (13 - 9) * 60     # 240 minutes (13:00)
    eric_blocked2_start = (14 - 9) * 60   # 300 minutes (14:00)
    eric_blocked2_end = (15 - 9) * 60     # 360 minutes (15:00)
    
    # Constraints for Eric: meeting must not overlap with blocked times
    s.add(Or(
        start + duration <= eric_blocked1_start,
        start >= eric_blocked1_end
    ))
    s.add(Or(
        start + duration <= eric_blocked2_start,
        start >= eric_blocked2_end
    ))
    
    # Henry's meetings in minutes from 9:00
    henry_meetings = [
        ((9.5 - 9) * 60, (10 - 9) * 60),        # 9:30-10:00 -> 30-60
        ((10.5 - 9) * 60, (11 - 9) * 60),       # 10:30-11:00 -> 90-120
        ((11.5 - 9) * 60, (12.5 - 9) * 60),     # 11:30-12:30 -> 150-210
        ((13 - 9) * 60, (13.5 - 9) * 60),       # 13:00-13:30 -> 240-270
        ((14.5 - 9) * 60, (15 - 9) * 60),       # 14:30-15:00 -> 330-360
        ((16 - 9) * 60, (17 - 9) * 60)          # 16:00-17:00 -> 420-480
    ]
    
    # Constraints for Henry: meeting must not overlap with any scheduled meeting
    for mtg_start, mtg_end in henry_meetings:
        s.add(Or(
            start + duration <= mtg_start,
            start >= mtg_end
        ))
    
    # Minimize start time to get the earliest possible meeting (preferably before 10:00)
    s.minimize(start)
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        start_minutes = m[start].as_long()
        
        # Convert start_minutes back to time string
        hours = start_minutes // 60
        minutes = start_minutes % 60
        start_time = f"{9 + hours:02d}:{minutes:02d}"
        
        # Calculate end time
        end_minutes = start_minutes + duration
        end_hours = end_minutes // 60
        end_minutes = end_minutes % 60
        end_time = f"{9 + end_hours:02d}:{end_minutes:02d}"
        
        # Output the solution in the required format
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        # According to the problem, a solution exists, so this should not happen
        print("No solution found")

if __name__ == "__main__":
    main()