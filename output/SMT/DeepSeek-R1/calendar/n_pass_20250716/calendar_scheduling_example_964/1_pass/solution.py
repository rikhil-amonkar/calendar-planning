from z3 import Solver, Int, Implies, Or, And, sat

def main():
    s = Solver()
    
    day = Int('day')
    start = Int('start')
    
    # Day constraints: 0=Monday, 1=Tuesday, 2=Friday
    s.add(day >= 0)
    s.add(day <= 2)
    
    # Start time constraints: meeting must be within 9:00 to 17:00 and last 60 minutes
    s.add(start >= 0)
    s.add(start <= 420)  # 17:00 - 60 minutes = 16:00 (420 minutes from 9:00)
    
    # Betty's busy intervals per day (each interval is [start_minute, end_minute))
    betty_busy = {
        0: [(60, 90), (150, 210), (420, 450)],  # Monday
        1: [(30, 60), (90, 120), (180, 210), (270, 360), (450, 480)],  # Tuesday
        2: [(0, 60), (150, 180), (210, 240), (330, 360)]  # Friday
    }
    
    # Megan's busy intervals per day
    megan_busy = {
        0: [(0, 480)],  # Monday (entire day)
        1: [(0, 30), (60, 90), (180, 300), (360, 390), (420, 450)],  # Tuesday
        2: [(0, 480)]   # Friday (entire day)
    }
    
    # Add constraints for Betty's busy intervals
    for d, intervals in betty_busy.items():
        for (s_b, e_b) in intervals:
            # Ensure meeting does not overlap with any busy interval
            s.add(Implies(day == d, Or(start + 60 <= s_b, start >= e_b)))
    
    # Add constraints for Megan's busy intervals
    for d, intervals in megan_busy.items():
        for (s_b, e_b) in intervals:
            s.add(Implies(day == d, Or(start + 60 <= s_b, start >= e_b)))
    
    # Check if a solution exists
    if s.check() == sat:
        model = s.model()
        d_val = model[day].as_long()
        start_val = model[start].as_long()
        
        # Convert day value to string
        days = ["Monday", "Tuesday", "Friday"]
        day_str = days[d_val]
        
        # Calculate start time in HH:MM format
        total_minutes = start_val
        hours = 9 + total_minutes // 60
        minutes = total_minutes % 60
        start_time = f"{hours}:{minutes:02d}"
        
        # Calculate end time (start time + 60 minutes)
        end_minutes = total_minutes + 60
        end_hours = 9 + end_minutes // 60
        end_minutes %= 60
        end_time = f"{end_hours}:{end_minutes:02d}"
        
        print(f"Day: {day_str}")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()