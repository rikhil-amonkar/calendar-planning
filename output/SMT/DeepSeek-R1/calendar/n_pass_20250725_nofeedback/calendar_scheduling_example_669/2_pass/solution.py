from z3 import *

def main():
    s = Solver()
    
    # Variables: day (0=Monday, 1=Tuesday), start_minute (minutes from 9:00)
    day = Int('day')
    start_minute = Int('start_minute')
    
    # Day must be Monday (0) or Tuesday (1)
    s.add(Or(day == 0, day == 1))
    
    # Meeting must be within 9:00-17:00 and last 30 minutes
    s.add(start_minute >= 0)        # 9:00 = 0 minutes
    s.add(start_minute <= 8*60)     # 17:00 is 8 hours from 9:00 (480 minutes), meeting must start by 16:30 (450 minutes)
    
    # Jean's constraints (only apply on Tuesday)
    # Busy: 11:30-12:00 (150-180 min) and 16:00-16:30 (420-450 min)
    jean_tue = Or(
        start_minute + 30 <= 150,   # Ends by 11:30
        And(start_minute >= 180, start_minute + 30 <= 420),  # Between 12:00-16:00
        start_minute >= 450          # At or after 16:30
    )
    s.add(If(day == 1, jean_tue, True))
    
    # Doris's constraints
    # Monday free slots: 
    #   11:30-12:00 (must start exactly at 11:30) 
    #   12:30-13:30 (must start between 12:30-13:00)
    doris_mon = Or(
        start_minute == 150,        # Only 11:30 start works for first slot
        And(210 <= start_minute, start_minute <= 240)  # 12:30-13:00 starts
    )
    # Tuesday: completely busy
    doris_tue = False
    s.add(If(day == 0, doris_mon, doris_tue))
    
    # Doris's preference: no Monday meetings ending after 14:00 (14:00 = 300 min)
    s.add(If(day == 0, start_minute + 30 <= 300, True))
    
    if s.check() == sat:
        m = s.model()
        d = m[day].as_long()
        sm = m[start_minute].as_long()
        
        day_str = "Monday" if d == 0 else "Tuesday"
        
        # Calculate start time (HH:MM)
        start_hour = 9 + sm // 60
        start_min = sm % 60
        start_time = f"{start_hour:02d}:{start_min:02d}"
        
        # Calculate end time (start + 30 min)
        end_minutes = sm + 30
        end_hour = 9 + end_minutes // 60
        end_min = end_minutes % 60
        end_time = f"{end_hour:02d}:{end_min:02d}"
        
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()