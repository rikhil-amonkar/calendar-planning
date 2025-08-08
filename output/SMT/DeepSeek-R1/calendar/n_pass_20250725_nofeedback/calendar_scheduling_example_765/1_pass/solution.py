from z3 import *

def main():
    # Create the solver
    s = Solver()
    
    # Day variable: 0 = Monday, 1 = Tuesday, 2 = Wednesday
    day = Int('day')
    # Start time in minutes from 9:00 (0 to 450 inclusive, since 450+30=480 minutes = 8 hours = 17:00-9:00)
    start = Int('start')
    
    # Constraints on day: must be 0, 1, or 2
    s.add(Or(day == 0, day == 1, day == 2))
    # Constraint on start: must be between 0 and 450 (inclusive)
    s.add(start >= 0, start <= 450)
    
    # Joyce is busy all day on Tuesday, so exclude Tuesday
    s.add(day != 1)
    
    # Joyce prefers not to meet on Monday before 12:00 -> we model as a hard constraint: if Monday, start >= 180 (minutes, since 12:00 - 9:00 = 3 hours = 180 minutes)
    s.add(If(day == 0, start >= 180, True))
    
    # Define busy intervals for Joshua: day -> list of (start_busy, end_busy) in minutes from 9:00
    joshua_busy = {
        0: [(360, 390)],   # Monday: 15:00-15:30
        1: [(150, 180), (240, 270), (330, 360)],  # Tuesday: 11:30-12:00, 13:00-13:30, 14:30-15:00
        2: []               # Wednesday: free
    }
    
    # Define busy intervals for Joyce
    joyce_busy = {
        0: [(0, 30), (60, 120), (150, 180), (240, 360), (390, 480)],  # Monday: 9:00-9:30, 10:00-11:00, 11:30-12:30, 13:00-15:00, 15:30-17:00
        1: [(0, 480)],   # Tuesday: entire day
        2: [(0, 30), (60, 120), (210, 390), (420, 450)]  # Wednesday: 9:00-9:30, 10:00-11:00, 12:30-15:30, 16:00-16:30
    }
    
    # Add constraints for Joshua's busy intervals
    for d, intervals in joshua_busy.items():
        for (s_busy, e_busy) in intervals:
            # For the current day `d`, ensure the meeting [start, start+30] does not overlap [s_busy, e_busy]
            s.add(If(day == d, Or(start + 30 <= s_busy, start >= e_busy), True))
            
    # Add constraints for Joyce's busy intervals
    for d, intervals in joyce_busy.items():
        for (s_busy, e_busy) in intervals:
            s.add(If(day == d, Or(start + 30 <= s_busy, start >= e_busy), True))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        d_val = m[day].as_long()
        start_val = m[start].as_long()
        
        # Map day value to string
        days = ["Monday", "Tuesday", "Wednesday"]
        day_str = days[d_val]
        
        # Calculate start time in HH:MM
        total_minutes_start = start_val
        hours_start = 9 + total_minutes_start // 60
        minutes_start = total_minutes_start % 60
        start_time_str = f"{hours_start:02d}:{minutes_start:02d}"
        
        # Calculate end time (start + 30 minutes)
        total_minutes_end = total_minutes_start + 30
        hours_end = 9 + total_minutes_end // 60
        minutes_end = total_minutes_end % 60
        end_time_str = f"{hours_end:02d}:{minutes_end:02d}"
        
        # Output the solution
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()