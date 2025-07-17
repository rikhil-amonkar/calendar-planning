from z3 import *

def main():
    # Initialize variables
    day = Int('day')
    start_time = Int('start_time')
    
    # Busy intervals in minutes (half-open [start, end))
    robert_busy = {
        0: [(660, 690), (840, 870), (930, 960)],  # Monday: 11:00-11:30, 14:00-14:30, 15:30-16:00
        1: [(630, 660), (900, 930)],               # Tuesday: 10:30-11:00, 15:00-15:30
        2: [(600, 660), (690, 720), (750, 780), (810, 840), (900, 930), (960, 990)]  # Wednesday: 10:00-11:00, 11:30-12:00, 12:30-13:00, 13:30-14:00, 15:00-15:30, 16:00-16:30
    }
    
    ralph_busy = {
        0: [(600, 810), (840, 870), (900, 1020)],  # Monday: 10:00-13:30, 14:00-14:30, 15:00-17:00
        1: [(540, 570), (600, 630), (660, 690), (720, 780), (840, 930), (960, 1020)],  # Tuesday: 9:00-9:30, 10:00-10:30, 11:00-11:30, 12:00-13:00, 14:00-15:30, 16:00-17:00
        2: [(630, 660), (690, 720), (780, 870), (990, 1020)]  # Wednesday: 10:30-11:00, 11:30-12:00, 13:00-14:30, 16:30-17:00
    }
    
    # Setup optimizer
    opt = Optimize()
    opt.add(day >= 0, day <= 2)
    opt.add(start_time >= 540, start_time <= 990)  # 540=9:00, 990=16:30 (since meeting ends at start+30 <= 1020=17:00)
    
    # Add constraints for Robert's busy times
    for day_index, intervals in robert_busy.items():
        for (b_start, b_end) in intervals:
            opt.add(If(day == day_index, Or(start_time + 30 <= b_start, start_time >= b_end), True)
    
    # Add constraints for Ralph's busy times
    for day_index, intervals in ralph_busy.items():
        for (b_start, b_end) in intervals:
            opt.add(If(day == day_index, Or(start_time + 30 <= b_start, start_time >= b_end), True)
    
    # Minimize: lexicographic (day, start_time)
    total = day * 10000 + start_time
    opt.minimize(total)
    
    # Solve
    if opt.check() == sat:
        m = opt.model()
        d = m[day].as_long()
        s_time = m[start_time].as_long()
        
        # Map day index to string
        days = ["Monday", "Tuesday", "Wednesday"]
        day_str = days[d]
        
        # Format start time
        start_hours = s_time // 60
        start_minutes = s_time % 60
        start_str = f"{start_hours:02d}:{start_minutes:02d}"
        
        # Format end time (start_time + 30 minutes)
        end_time = s_time + 30
        end_hours = end_time // 60
        end_minutes = end_time % 60
        end_str = f"{end_hours:02d}:{end_minutes:02d}"
        
        # Output solution
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_str}")
        print(f"End Time: {end_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()