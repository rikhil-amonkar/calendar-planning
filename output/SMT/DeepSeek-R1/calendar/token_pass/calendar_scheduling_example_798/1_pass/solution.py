from z3 import *

def main():
    # Initialize solver with optimization
    opt = Optimize()
    
    # Meeting day: 0=Monday, 1=Tuesday, 2=Wednesday
    day = Int('day')
    start_time = Int('start_time')  # in minutes from 00:00
    
    # Work hours: 9:00 to 17:00 (540 to 1020 minutes)
    min_time = 540
    max_time = 1020
    meeting_duration = 30
    
    # Constraints for day and start_time
    opt.add(day >= 0)
    opt.add(day <= 2)
    opt.add(start_time >= min_time)
    opt.add(start_time <= max_time - meeting_duration)
    
    # Busy intervals for Nancy and Jose (in minutes from 00:00)
    nancy_busy = {
        0: [(600, 630), (690, 750), (810, 840), (870, 930), (960, 1020)],
        1: [(570, 630), (660, 690), (720, 750), (780, 810), (930, 960)],
        2: [(600, 690), (810, 960)]
    }
    
    jose_busy = {
        0: [(540, 1020)],
        1: [(540, 1020)],
        2: [(540, 570), (600, 750), (810, 870), (900, 1020)]
    }
    
    # For each day, add constraints that the meeting does not overlap with busy intervals
    for d in range(3):
        # Nancy's constraints for day d
        for interval in nancy_busy[d]:
            opt.add(If(day == d, 
                       Or(start_time >= interval[1], start_time + meeting_duration <= interval[0]), 
                       True))
        
        # Jose's constraints for day d
        for interval in jose_busy[d]:
            opt.add(If(day == d, 
                       Or(start_time >= interval[1], start_time + meeting_duration <= interval[0]), 
                       True))
    
    # Minimize: prioritize earlier day, then earlier start time
    objective = day * 1440 + start_time  # 1440 minutes per day
    opt.minimize(objective)
    
    # Check satisfiability
    if opt.check() == sat:
        m = opt.model()
        d_val = m[day].as_long()
        start_val = m[start_time].as_long()
        
        # Map day integer to string
        days = ["Monday", "Tuesday", "Wednesday"]
        day_str = days[d_val]
        
        # Convert start and end times to HH:MM format
        start_hour = start_val // 60
        start_minute = start_val % 60
        end_val = start_val + meeting_duration
        end_hour = end_val // 60
        end_minute = end_val % 60
        
        time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
        print(f"{day_str} {time_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()