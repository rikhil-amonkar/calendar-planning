from z3 import *

def main():
    # Initialize solver
    opt = Optimize()
    
    # Day variable: 0 for Monday, 1 for Tuesday
    d = Int('d')
    # Start time in minutes from midnight (00:00)
    start = Int('start')
    
    # Work hours: 9:00 to 17:00 -> 540 to 1020 minutes
    # Meeting duration: 30 minutes -> so start must be at or before 990 (since 990 + 30 = 1020)
    opt.add(Or(d == 0, d == 1))
    opt.add(start >= 540)
    opt.add(start <= 990)
    
    # Bobby's busy intervals in minutes (day 0: Monday, day 1: Tuesday)
    bobby_busy = {
        0: [(14*60 + 30, 15*60)],  # Monday: 14:30-15:00
        1: [(9*60, 11*60 + 30),    # Tuesday: 9:00-11:30
            (12*60, 12*60 + 30),   # 12:00-12:30
            (13*60, 15*60),         # 13:00-15:00
            (15*60 + 30, 17*60)]    # 15:30-17:00
    }
    
    # Michael's busy intervals
    michael_busy = {
        0: [(9*60, 10*60),         # Monday: 9:00-10:00
            (10*60 + 30, 13*60 + 30), # 10:30-13:30
            (14*60, 15*60),          # 14:00-15:00
            (15*60 + 30, 17*60)],     # 15:30-17:00
        1: [(9*60, 10*60 + 30),     # Tuesday: 9:00-10:30
            (11*60, 11*60 + 30),    # 11:00-11:30
            (12*60, 14*60),         # 12:00-14:00
            (15*60, 16*60),         # 15:00-16:00
            (16*60 + 30, 17*60)]    # 16:30-17:00
    }
    
    # Add constraints for Bobby's busy intervals
    for day, intervals in bobby_busy.items():
        for (busy_start, busy_end) in intervals:
            # If meeting is on `day`, ensure no overlap with busy interval
            opt.add(If(d == day, Or(start + 30 <= busy_start, start >= busy_end), True))
    
    # Add constraints for Michael's busy intervals
    for day, intervals in michael_busy.items():
        for (busy_start, busy_end) in intervals:
            opt.add(If(d == day, Or(start + 30 <= busy_start, start >= busy_end), True))
    
    # Minimize total minutes from start of Monday (00:00 Monday)
    total_minutes = d * 24 * 60 + start  # 24*60 = 1440 minutes per day
    opt.minimize(total_minutes)
    
    # Check for solution
    if opt.check() == sat:
        model = opt.model()
        day_val = model[d].as_long()
        start_val = model[start].as_long()
        
        # Convert day value to string
        day_str = "Monday" if day_val == 0 else "Tuesday"
        
        # Convert start minutes to HH:MM
        hours = start_val // 60
        minutes = start_val % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        
        # Calculate end time (start + 30 minutes)
        end_minutes = start_val + 30
        end_hours = end_minutes // 60
        end_minutes = end_minutes % 60
        end_time = f"{end_hours:02d}:{end_minutes:02d}"
        
        # Print solution in required format
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()