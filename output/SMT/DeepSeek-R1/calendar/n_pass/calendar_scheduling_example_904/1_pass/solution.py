from z3 import *

def main():
    day = Int('day')
    start_time = Int('start_time')
    
    opt = Optimize()
    
    # Day constraints: only Tuesday (1) is allowed
    opt.add(day == 1)
    
    # Time constraints: meeting must be within 9:00 to 17:00
    opt.add(start_time >= 540)   # 9:00
    opt.add(start_time <= 990)   # 16:30 (since 990+30=1020=17:00)
    
    # Bradley: on Tuesday, must be after 12:00 (720 minutes)
    opt.add(start_time >= 720)
    
    # Daniel's busy intervals on Tuesday (in minutes): (780,810), (930,960), (990,1020)
    # Bradley's busy intervals on Tuesday (in minutes): (720,780), (810,840), (930,990)
    # Constraints for Daniel: meeting must not overlap with any busy interval
    opt.add(Or(start_time + 30 <= 780, start_time >= 810))
    opt.add(Or(start_time + 30 <= 930, start_time >= 960))
    opt.add(Or(start_time + 30 <= 990, start_time >= 1020))
    
    # Constraints for Bradley: meeting must not overlap with any busy interval
    opt.add(Or(start_time + 30 <= 720, start_time >= 780))
    opt.add(Or(start_time + 30 <= 810, start_time >= 840))
    opt.add(Or(start_time + 30 <= 930, start_time >= 990))
    
    # Minimize start time to get the earliest meeting
    opt.minimize(start_time)
    
    if opt.check() == sat:
        m = opt.model()
        d_val = m[day].as_long()
        st_val = m[start_time].as_long()
        end_val = st_val + 30
        
        # Convert start time to HH:MM format
        start_hour = st_val // 60
        start_minute = st_val % 60
        start_str = f"{start_hour:02d}:{start_minute:02d}"
        
        # Convert end time to HH:MM format
        end_hour = end_val // 60
        end_minute = end_val % 60
        end_str = f"{end_hour:02d}:{end_minute:02d}"
        
        # Map day index to string
        days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
        day_str = days[d_val]
        
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_str}")
        print(f"End Time: {end_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()