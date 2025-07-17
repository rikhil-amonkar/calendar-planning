from z3 import *

def main():
    # Initialize Z3 solver
    s = Solver()
    
    # Define variables: day (0 for Monday, 1 for Tuesday) and start_minute (minutes from 9:00)
    day = Int('day')
    start_minute = Int('start_minute')
    
    # Day must be Monday (0) or Tuesday (1)
    s.add(Or(day == 0, day == 1))
    
    # Start minute must be between 0 and 450 (inclusive) to allow a 30-minute meeting within 9:00-17:00
    s.add(start_minute >= 0, start_minute <= 450)
    
    # Margaret does not want to meet on Monday, so enforce Tuesday
    s.add(day == 1)
    
    # On Tuesday, Margaret does not want to meet before 14:30 (330 minutes from 9:00)
    s.add(start_minute >= 330)
    
    # Margaret's busy intervals on Tuesday (in minutes from 9:00)
    margaret_tuesday_busy = [(180, 210)]  # 12:00 to 12:30
    
    # Alexis's busy intervals on Tuesday
    alexis_tuesday_busy = [(0, 30), (60, 90), (300, 450)]  # 9:00-9:30, 10:00-10:30, 14:00-16:30
    
    # Add constraints to avoid Margaret's busy intervals
    for (busy_start, busy_end) in margaret_tuesday_busy:
        s.add(Or(start_minute + 30 <= busy_start, start_minute >= busy_end))
    
    # Add constraints to avoid Alexis's busy intervals
    for (busy_start, busy_end) in alexis_tuesday_busy:
        s.add(Or(start_minute + 30 <= busy_start, start_minute >= busy_end))
    
    # Check for a feasible solution
    if s.check() == sat:
        m = s.model()
        d = m[day].as_long()
        sm = m[start_minute].as_long()
        
        # Convert day index to string
        day_str = "Tuesday" if d == 1 else "Monday"
        
        # Calculate start time in HH:MM format
        total_minutes_start = sm
        hours_start = 9 + total_minutes_start // 60
        minutes_start = total_minutes_start % 60
        start_time = f"{hours_start:02d}:{minutes_start:02d}"
        
        # Calculate end time (start time + 30 minutes)
        total_minutes_end = sm + 30
        hours_end = 9 + total_minutes_end // 60
        minutes_end = total_minutes_end % 60
        end_time = f"{hours_end:02d}:{minutes_end:02d}"
        
        # Output the solution in the required format
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()