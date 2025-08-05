from z3 import *

def main():
    # Define the busy intervals for each participant in minutes from 9:00
    busy_intervals = {
        "Jacqueline": [(0, 30), (120, 150), (210, 240)],
        "Harold": [(60, 90)],
        "Arthur": [(0, 30), (60, 210)],
        "Kelly": [(0, 30), (60, 120), (150, 210)]
    }
    
    # Create a solver instance
    s = Solver()
    
    # Define the start time variable (in minutes from 9:00)
    start = Int('start')
    
    # Meeting must be within work hours (9:00 to 17:00) and end by 13:00 (240 minutes from 9:00)
    s.add(start >= 0)
    s.add(start + 30 <= 240)  # Harold's constraint: meeting ends by 13:00
    s.add(start <= 210)        # Because start + 30 <= 240 implies start <= 210
    
    # Add constraints for each participant's busy intervals
    for person, intervals in busy_intervals.items():
        for (s_busy, e_busy) in intervals:
            # Meeting [start, start+30) must not overlap with [s_busy, e_busy)
            s.add(Or(start + 30 <= s_busy, start >= e_busy))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        start_minutes = m[start].as_long()
        
        # Convert start time to HH:MM format
        start_hour = 9 + start_minutes // 60
        start_minute = start_minutes % 60
        start_time = f"{start_hour:02d}:{start_minute:02d}"
        
        # Calculate end time (start + 30 minutes)
        end_minutes = start_minutes + 30
        end_hour = 9 + end_minutes // 60
        end_minute = end_minutes % 60
        end_time = f"{end_hour:02d}:{end_minute:02d}"
        
        # Output the solution
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()