from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Define day and start time variables
    day = Int('day')
    start_minutes = Int('start_minutes')
    
    # Meeting duration in minutes
    duration = 60
    
    # Work hours: 9:00 to 17:00 (540 to 1020 minutes)
    work_start = 540
    work_end = 1020
    
    # Day mapping: Monday=0, Tuesday=1, Wednesday=2, Thursday=3
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    
    # Add constraints for day and time bounds
    s.add(day >= 0, day <= 3)
    s.add(start_minutes >= work_start)
    s.add(start_minutes + duration <= work_end)
    
    # Megan's busy intervals (day, start_min, end_min)
    megan_busy = [
        (0, 780, 810), (0, 840, 930),
        (1, 540, 570), (1, 720, 750), (1, 960, 1020),
        (2, 570, 600), (2, 630, 690), (2, 750, 840), (2, 960, 990),
        (3, 810, 870), (3, 900, 930)
    ]
    
    # Daniel's busy intervals
    daniel_busy = [
        (0, 600, 690), (0, 750, 900),
        (1, 540, 600), (1, 630, 1020),
        (2, 540, 600), (2, 630, 690), (2, 720, 1020),
        (3, 540, 720), (3, 750, 870), (3, 900, 930), (3, 960, 1020)
    ]
    
    # Function to add no-overlap constraints
    def add_no_overlap(busy_intervals):
        for d, bus_start, bus_end in busy_intervals:
            # If meeting is on this day, ensure no overlap with busy interval
            s.add(Not(And(day == d,
                          start_minutes < bus_end,
                          start_minutes + duration > bus_start)))
    
    # Add constraints for both participants
    add_no_overlap(megan_busy)
    add_no_overlap(daniel_busy)
    
    # Find earliest time (minimize day and then start time)
    objective = day * (24 * 60) + start_minutes
    opt = Optimize()
    opt.add(s.assertions())
    opt.minimize(objective)
    
    # Check and output solution
    if opt.check() == sat:
        m = opt.model()
        d_val = m.eval(day).as_long()
        start_val = m.eval(start_minutes).as_long()
        end_val = start_val + duration
        
        # Convert minutes to HH:MM format
        def fmt_time(m):
            h = m // 60
            m = m % 60
            return f"{h:02d}:{m:02d}"
        
        day_str = days[d_val]
        start_str = fmt_time(start_val)
        end_str = fmt_time(end_val)
        print(f"{day_str} {start_str}:{end_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()