from z3 import Int, Solver, And, Or, Implies, sat

def main():
    # Meeting parameters
    duration = 30                # meeting duration in minutes
    work_start = 0               # 9:00 represented as 0 minutes offset
    work_end = 480               # 17:00 is 480 minutes after 9:00
    latest_start = work_end - duration  # meeting must finish by 17:00
    
    # Day mapping: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    
    # SMT variables: day and start time (in minutes after 9:00)
    day = Int("day")       # allowed domain 0..4
    start = Int("start")   # meeting start in minutes (0 = 9:00, 450 = 16:30)
    
    s = Solver()
    
    # Domain constraints
    s.add(day >= 0, day <= 4)
    s.add(start >= work_start, start <= latest_start)
    
    # Eric prefers to avoid more meetings on Wednesday.
    # Since Eric is fully busy on Monday, Tuesday, and Thursday,
    # the only possible days are Wednesday and Friday.
    # Force the meeting to be scheduled on a day other than Wednesday.
    s.add(day != 2)
    
    # Helper function: For a given busy day and busy interval (in minutes relative to 9:00),
    # add a constraint that if the meeting is on that day then it must not overlap the interval.
    def add_busy_constraints(solver, busy_day, busy_intervals):
        for (bstart, bend) in busy_intervals:
            solver.add(Implies(day == busy_day, Or(start + duration <= bstart, start >= bend)))
    
    # Eugene's busy intervals (times are offset from 9:00):
    # Monday (day=0): 11:00-12:00, 13:30-14:00, 14:30-15:00, 16:00-16:30
    # Wednesday (day=2): 9:00-9:30, 11:00-11:30, 12:00-12:30, 13:30-15:00
    # Thursday (day=3): 9:30-10:00, 11:00-12:30
    # Friday (day=4): 10:30-11:00, 12:00-12:30, 13:00-13:30
    eugene_busy = {
        0: [(120, 180), (270, 300), (330, 360), (420, 450)],
        2: [(0, 30), (120, 150), (180, 210), (270, 360)],
        3: [(30, 60), (120, 210)],
        4: [(90, 120), (180, 210), (240, 270)]
    }
    for d, intervals in eugene_busy.items():
        add_busy_constraints(s, d, intervals)
    
    # Eric's busy intervals:
    # Monday (day=0): 9:00-17:00
    # Tuesday (day=1): 9:00-17:00
    # Wednesday (day=2): 9:00-11:30, 12:00-14:00, 14:30-16:30
    # Thursday (day=3): 9:00-17:00
    # Friday (day=4): 9:00-11:00, 11:30-17:00
    eric_busy = {
        0: [(0, 480)],
        1: [(0, 480)],
        2: [(0, 150), (180, 300), (330, 450)],
        3: [(0, 480)],
        4: [(0, 120), (150, 480)]
    }
    for d, intervals in eric_busy.items():
        add_busy_constraints(s, d, intervals)
    
    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        meeting_day = m[day].as_long()
        meeting_start = m[start].as_long()
        meeting_end = meeting_start + duration
        
        # Convert minutes (offset from 9:00) to actual clock time
        start_hour = 9 + meeting_start // 60
        start_min  = meeting_start % 60
        end_hour   = 9 + meeting_end // 60
        end_min    = meeting_end % 60
        
        print(f"{days[meeting_day]} {start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}")
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()