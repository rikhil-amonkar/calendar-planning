from z3 import *

def main():
    # Define the variables
    day = Int('day')
    start = Int('start')
    
    s = Solver()
    
    # Constraints for day and start time
    s.add(day >= 0, day <= 3)
    s.add(start >= 0, start <= 450)  # 450 because 480-30=450 (meeting duration 30 minutes)
    
    # Define busy intervals for Ruth (half-open intervals [start, end))
    busy_intervals = {
        0: [(0, 480)],  # Monday: busy from 0 to 480 minutes (9:00-17:00)
        1: [(0, 480)],  # Tuesday: same
        2: [(0, 480)],  # Wednesday: same
        3: [(0, 120), (150, 330), (360, 480)]  # Thursday: busy intervals
    }
    
    # Add constraints for each day and each busy interval
    for d, intervals in busy_intervals.items():
        for (b_start, b_end) in intervals:
            # The meeting [start, start+30] must not overlap [b_start, b_end)
            s.add(Or(day != d, Or(start + 30 <= b_start, start >= b_end)))
    
    # Julie's preference: avoid meetings on Thursday before 11:30 (150 minutes from 9:00)
    s.add(Or(day != 3, start + 30 > 150))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        d_val = m[day].as_long()
        start_val = m[start].as_long()
        
        # Map day index to day name
        days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
        day_name = days[d_val]
        
        # Calculate start time in hours and minutes
        total_minutes_start = start_val
        hours_start = 9 + total_minutes_start // 60
        minutes_start = total_minutes_start % 60
        start_time = f"{hours_start:02d}:{minutes_start:02d}"
        
        # Calculate end time (start + 30 minutes)
        total_minutes_end = start_val + 30
        hours_end = 9 + total_minutes_end // 60
        minutes_end = total_minutes_end % 60
        end_time = f"{hours_end:02d}:{minutes_end:02d}"
        
        # Print the solution
        print(f"Day: {day_name}")
        print(f"Start: {start_time}")
        print(f"End: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()