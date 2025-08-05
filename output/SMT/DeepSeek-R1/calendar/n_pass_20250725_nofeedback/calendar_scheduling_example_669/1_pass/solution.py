from z3 import *

def main():
    # Create solver
    s = Solver()
    
    # Variables: day (0=Monday, 1=Tuesday), start_minute (minutes from 9:00)
    day = Int('day')
    start_minute = Int('start_minute')
    
    # Day must be Monday (0) or Tuesday (1)
    s.add(Or(day == 0, day == 1))
    
    # Meeting duration is 30 minutes, so start_minute must be between 0 and 450 (since 480 - 30 = 450)
    s.add(start_minute >= 0)
    s.add(start_minute <= 450)
    
    # Jean's constraints: only on Tuesday
    # Avoid 11:30-12:00 (150 to 180 minutes from 9:00) and 16:00-16:30 (420 to 450 minutes)
    jean_tue = Or(
        start_minute + 30 <= 150,  # Meeting ends by 11:30
        And(start_minute >= 180, start_minute + 30 <= 420),  # Between 12:00 and 16:00
        start_minute >= 450  # At or after 16:30
    )
    s.add(If(day == 1, jean_tue, True))  # Only apply if Tuesday
    
    # Doris's constraints
    # On Monday: free slots are 11:30-12:00 (150 to 180 minutes) and 12:30-13:30 (210 to 270 minutes)
    doris_mon = Or(
        And(150 <= start_minute, start_minute < 180),
        And(210 <= start_minute, start_minute < 270)
    )
    # On Tuesday: no free time (entire day busy)
    doris_tue = False
    s.add(If(day == 0, doris_mon, doris_tue))
    
    # Doris's preference: on Monday, meeting must end by 14:00 (300 minutes from 9:00)
    s.add(If(day == 0, start_minute + 30 <= 300, True))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        d = m[day].as_long()
        sm = m[start_minute].as_long()
        
        # Convert day to string
        day_str = "Monday" if d == 0 else "Tuesday"
        
        # Calculate start time in HH:MM
        start_hour = 9 + sm // 60
        start_min = sm % 60
        start_time = f"{start_hour:02d}:{start_min:02d}"
        
        # Calculate end time (start time + 30 minutes)
        end_minutes = sm + 30
        end_hour = 9 + end_minutes // 60
        end_min = end_minutes % 60
        end_time = f"{end_hour:02d}:{end_min:02d}"
        
        # Output the solution
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()