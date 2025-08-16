from z3 import *

def schedule_meeting():
    s = Solver()
    
    day = Int('day')
    start = Int('start')
    
    # Day must be 0 (Monday), 1 (Tuesday), or 2 (Wednesday)
    s.add(Or(day == 0, day == 1, day == 2))
    
    # Start time between 9:00 (540 min) and 16:30 (990 min)
    s.add(And(540 <= start, start <= 990))
    
    # Tyler's busy periods (day, start_min, end_min)
    tyler_busy = [
        (1, 9*60, 9*60 + 30),           # Tuesday 9:00-9:30
        (1, 14*60 + 30, 14*60 + 30 + 30),# Tuesday 14:30-15:00
        (2, 10*60 + 30, 10*60 + 60),     # Wednesday 10:30-11:00
        (2, 12*60 + 30, 12*60 + 60),     # Wednesday 12:30-13:00
        (2, 13*60 + 30, 13*60 + 60),     # Wednesday 13:30-14:00
        (2, 16*60 + 30, 16*60 + 60)      # Wednesday 16:30-17:00
    ]
    
    for d, b_start, b_end in tyler_busy:
        s.add(Implies(day == d, Or(start + 30 <= b_start, start >= b_end)))
    
    # Ruth's busy periods (day, start_min, end_min)
    ruth_busy = [
        (0, 9*60, 10*60),               # Monday 9:00-10:00
        (0, 10*60 + 30, 12*60),         # Monday 10:30-12:00
        (0, 12*60 + 30, 14*60 + 30),    # Monday 12:30-14:30
        (0, 15*60, 16*60),              # Monday 15:00-16:00
        (0, 16*60 + 30, 17*60),         # Monday 16:30-17:00
        (1, 9*60, 17*60),               # Tuesday 9:00-17:00
        (2, 9*60, 17*60)                # Wednesday 9:00-17:00
    ]
    
    for d, b_start, b_end in ruth_busy:
        s.add(Implies(day == d, Or(start + 30 <= b_start, start >= b_end)))
    
    # Tyler's preference: avoid Monday before 16:00
    s.add(Or(day != 0, start >= 16 * 60))
    
    if s.check() == sat:
        m = s.model()
        day_val = m[day].as_long()
        start_val = m[start].as_long()
        end_val = start_val + 30
        
        days = ['Monday', 'Tuesday', 'Wednesday']
        start_hours = start_val // 60
        start_mins = start_val % 60
        end_hours = end_val // 60
        end_mins = end_val % 60
        
        print("SOLUTION:")
        print(f"Day: {days[day_val]}")
        print(f"Start Time: {start_hours:02d}:{start_mins:02d}")
        print(f"End Time: {end_hours:02d}:{end_mins:02d}")
    else:
        print("No solution found")

schedule_meeting()