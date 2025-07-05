from z3 import *

def find_meeting_time():
    # Create a solver instance
    s = Solver()
    
    # Define the start time as an integer (minutes since 9:00)
    start = Int('start')
    
    # Meeting duration is 30 minutes
    duration = 30
    
    # Total working hours from 9:00 to 17:00 (480 minutes)
    total_minutes = 8 * 60  # 9:00-17:00 is 8 hours
    
    # Constraint: start time must be within working hours (0 to 480 - duration)
    s.add(start >= 0)
    s.add(start <= total_minutes - duration)
    
    # Convert start time to hours and minutes for easier comparison
    start_hour = start / 60
    start_minute = start % 60
    
    # Frank's constraint: meeting must start at or before 9:30 (so start <= 30 minutes)
    s.add(start <= 30)
    
    # Define busy intervals for each participant (in minutes since 9:00)
    emily_busy = [
        (60, 90),    # 10:00-10:30
        (150, 210),   # 11:30-12:30
        (300, 360),   # 14:00-15:00
        (420, 450)    # 16:00-16:30
    ]
    
    melissa_busy = [
        (30, 60),    # 9:30-10:00
        (330, 360)    # 14:30-15:00
    ]
    
    frank_busy = [
        (60, 90),    # 10:00-10:30
        (120, 150),   # 11:00-11:30
        (210, 240),   # 12:30-13:00
        (270, 330),   # 13:30-14:30
        (360, 420),   # 15:00-16:00
        (450, 480)    # 16:30-17:00
    ]
    
    # Function to check if the meeting overlaps with any busy interval
    def no_overlap(busy_intervals):
        return And([Or(start + duration <= begin, start >= end) for (begin, end) in busy_intervals])
    
    # Add constraints for each participant
    s.add(no_overlap(emily_busy))
    s.add(no_overlap(melissa_busy))
    s.add(no_overlap(frank_busy))
    
    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        start_time_min = m[start].as_long()
        
        # Convert start time back to HH:MM format
        start_hour = 9 + start_time_min // 60
        start_minute = start_time_min % 60
        end_time_min = start_time_min + duration
        end_hour = 9 + end_time_min // 60
        end_minute = end_time_min % 60
        
        # Format the output
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_hour:02d}:{start_minute:02d}")
        print(f"End Time: {end_hour:02d}:{end_minute:02d}")
    else:
        print("No solution found")

find_meeting_time()