from z3 import *

def main():
    # Define the busy intervals in minutes (relative to 9:00)
    busy_intervals = {
        'Andrea': [(30, 90), (270, 330)],
        'Ruth': [(210, 240)],
        'Steven': [(60, 90), (120, 150), (180, 210), (270, 300), (360, 420)],
        'Kyle': [(0, 30), (90, 180), (210, 240), (270, 360), (390, 420), (450, 480)],
        'Elijah': [(0, 120), (150, 240), (270, 300), (390, 420), (450, 480)],
        'Lori': [(0, 30), (60, 150), (180, 270), (300, 420), (450, 480)]
    }
    
    s = Solver()
    start = Int('start')
    s.add(start >= 0, start <= 450)  # Meeting must start between 0 and 450 minutes (inclusive)
    
    # Add constraints for each participant's busy intervals
    for intervals in busy_intervals.values():
        for (b_start, b_end) in intervals:
            s.add(Or(start + 30 <= b_start, start >= b_end))
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        
        # Convert start time from minutes to HH:MM format
        hours = 9 + start_min // 60
        minutes = start_min % 60
        start_time = f"{hours}:{minutes:02d}"
        
        # Calculate end time (start time + 30 minutes)
        end_min = start_min + 30
        end_hours = 9 + end_min // 60
        end_minutes = end_min % 60
        end_time = f"{end_hours}:{end_minutes:02d}"
        
        # Output the solution
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()