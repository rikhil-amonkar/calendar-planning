from z3 import *

def main():
    # Create solver and variables
    s = Int('s')  # start time in minutes from 00:00
    d = Int('d')  # day: 0 for Monday, 1 for Tuesday
    
    solver = Solver()
    
    # Day must be 0 (Monday) or 1 (Tuesday)
    solver.add(Or(d == 0, d == 1))
    
    # Time constraints based on the day
    # Monday: 9:00 (540) to 17:00 (1020) inclusive, meeting duration 30 minutes -> s+30 <= 1020
    # Tuesday: 9:00 (540) to 16:30 (990) inclusive for end time -> s+30 <= 990
    solver.add(If(d == 0,
                 And(s >= 540, s + 30 <= 1020),
                 And(s >= 540, s + 30 <= 990)))
    
    # Define busy intervals (start, end) in minutes from 00:00 for each day
    # Format: (start_minutes, end_minutes) representing [start, end)
    busy_intervals = {
        0: [(540, 1020), (810, 840), (870, 900)],  # Monday: Lawrence's entire day and Jesse's meetings
        1: [(540, 570), (780, 810), (840, 900),     # Tuesday: Jesse's meetings
            (570, 630), (690, 750), (780, 810), (870, 900), (930, 990)]  # Lawrence's meetings
    }
    
    # Add constraints to avoid busy intervals for the chosen day
    for day_val, intervals in busy_intervals.items():
        for (b_start, b_end) in intervals:
            # If the current interval is for the chosen day (d), ensure no overlap
            # Non-overlap: meeting ends before busy interval starts OR meeting starts after busy interval ends
            solver.add(If(d == day_val,
                          Or(s + 30 <= b_start, s >= b_end),
                          True))
    
    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        d_val = model[d].as_long()
        s_val = model[s].as_long()
        
        # Convert day value to string
        day_str = "Monday" if d_val == 0 else "Tuesday"
        
        # Convert start time from minutes to HH:MM
        start_hour = s_val // 60
        start_minute = s_val % 60
        start_time = f"{start_hour:02d}:{start_minute:02d}"
        
        # Calculate end time
        end_minutes = s_val + 30
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        end_time = f"{end_hour:02d}:{end_minute:02d}"
        
        # Output the solution
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()