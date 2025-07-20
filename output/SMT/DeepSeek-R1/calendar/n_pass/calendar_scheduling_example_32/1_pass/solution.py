from z3 import *

def main():
    day = "Monday"
    work_start_minutes = 0    # 9:00
    work_end_minutes = 480    # 17:00 (8 hours * 60 minutes)
    meeting_duration = 30

    # Busy intervals in minutes from 9:00
    emily_busy = [
        (60, 90),    # 10:00-10:30
        (150, 210),  # 11:30-12:30
        (300, 360),  # 14:00-15:00
        (420, 450)   # 16:00-16:30
    ]
    melissa_busy = [
        (30, 60),    # 9:30-10:00
        (330, 360)   # 14:30-15:00
    ]
    frank_busy = [
        (60, 90),    # 10:00-10:30
        (120, 150),  # 11:00-11:30
        (210, 240),  # 12:30-13:00
        (270, 330),  # 13:30-14:30
        (360, 420),  # 15:00-16:00
        (450, 480)   # 16:30-17:00
    ]
    
    # Initialize Z3 solver and variables
    start = Int('start')
    end = start + meeting_duration
    s = Solver()
    
    # Meeting within work hours
    s.add(start >= work_start_minutes)
    s.add(end <= work_end_minutes)
    
    # Frank's constraint: meeting must end by 9:30 (30 minutes from 9:00)
    s.add(end <= 30)
    
    # Add constraints for each participant's busy intervals
    for a, b in emily_busy:
        s.add(Or(end <= a, start >= b))
    for a, b in melissa_busy:
        s.add(Or(end <= a, start >= b))
    for a, b in frank_busy:
        s.add(Or(end <= a, start >= b))
    
    # Check for solution
    if s.check() == sat:
        model = s.model()
        start_val = model[start].as_long()
        
        # Convert start time to HH:MM format
        total_minutes = start_val
        hours = total_minutes // 60
        minutes = total_minutes % 60
        actual_hour = 9 + hours
        start_time = f"{actual_hour:02d}:{minutes:02d}"
        
        # Calculate end time
        end_minutes = start_val + meeting_duration
        hours_end = end_minutes // 60
        minutes_end = end_minutes % 60
        actual_hour_end = 9 + hours_end
        end_time = f"{actual_hour_end:02d}:{minutes_end:02d}"
        
        # Output the solution
        print("SOLUTION:")
        print(f"Day: {day}")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()