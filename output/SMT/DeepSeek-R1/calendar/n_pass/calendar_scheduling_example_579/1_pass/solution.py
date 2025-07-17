from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Convert all times to minutes from 00:00
    work_start = 9 * 60   # 540 minutes (9:00)
    work_end = 17 * 60    # 1020 minutes (17:00)
    meeting_duration = 30
    helen_end_constraint = 15 * 60  # 900 minutes (15:00)
    
    # Christine's busy intervals (half-open: [start, end))
    christine_busy = [
        (11 * 60, 11 * 60 + 30),    # 11:00 to 11:30 -> [660, 690)
        (15 * 60, 15 * 60 + 30)     # 15:00 to 15:30 -> [900, 930)
    ]
    
    # Helen's busy intervals (half-open: [start, end))
    helen_busy = [
        (9 * 60 + 30, 10 * 60 + 30),  # 9:30 to 10:30 -> [570, 630)
        (11 * 60, 11 * 60 + 30),      # 11:00 to 11:30 -> [660, 690)
        (12 * 60, 12 * 60 + 30),      # 12:00 to 12:30 -> [720, 750)
        (13 * 60 + 30, 16 * 60),      # 13:30 to 16:00 -> [810, 960)
        (16 * 60 + 30, 17 * 60)       # 16:30 to 17:00 -> [990, 1020)
    ]
    
    # Define the start time variable (in minutes)
    S = Int('S')
    
    # Constraints for work hours and Helen's end constraint
    s.add(S >= work_start)
    s.add(S <= work_end - meeting_duration)  # Meeting must end by work_end
    s.add(S + meeting_duration <= helen_end_constraint)  # Meeting must end by 15:00
    
    # Constraints for Christine's busy intervals
    for start, end in christine_busy:
        # Meeting must not overlap: either ends before busy start or starts after busy end
        s.add(Or(S + meeting_duration <= start, S >= end))
    
    # Constraints for Helen's busy intervals
    for start, end in helen_busy:
        s.add(Or(S + meeting_duration <= start, S >= end))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        start_minutes = m[S].as_long()
        
        # Convert start minutes to HH:MM format
        start_hour = start_minutes // 60
        start_minute = start_minutes % 60
        start_time = f"{start_hour:02d}:{start_minute:02d}"
        
        # Calculate end time
        end_minutes = start_minutes + meeting_duration
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        end_time = f"{end_hour:02d}:{end_minute:02d}"
        
        # Output the solution
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()