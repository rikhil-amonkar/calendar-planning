from z3 import *

def schedule_meeting():
    s = Solver()
    
    day = Int('day')
    start = Int('start')
    
    # Day must be 0 (Monday), 1 (Tuesday), or 2 (Wednesday)
    s.add(Or(day == 0, day == 1, day == 2))
    
    # Start time must be between 0 and 450 minutes (9:00 to 17:00, 30 min meeting)
    s.add(And(start >= 0, start + 30 <= 480))
    
    # Tyler's preference: avoid Monday before 16:00 (420 minutes after 9:00)
    s.add(Implies(day == 0, start >= 420))
    
    # Tyler's busy times per day (day, [(start, end), ...])
    tyler_busy = [
        (1, [(0, 30), (330, 360)]),  # Tuesday
        (2, [(60, 90), (150, 180), (210, 240), (390, 420)])  # Wednesday
    ]
    
    # Ruth's busy times per day
    ruth_busy = [
        (0, [(0, 60), (90, 180), (210, 270), (360, 420), (450, 480)]),  # Monday
        (1, [(0, 480)]),  # Tuesday
        (2, [(0, 480)])   # Wednesday
    ]
    
    # Add constraints for Tyler's busy times
    for d, intervals in tyler_busy:
        for b_start, b_end in intervals:
            s.add(Implies(day == d, Or(start + 30 <= b_start, start >= b_end)))
    
    # Add constraints for Ruth's busy times
    for d, intervals in ruth_busy:
        for b_start, b_end in intervals:
            s.add(Implies(day == d, Or(start + 30 <= b_start, start >= b_end)))
    
    if s.check() == sat:
        m = s.model()
        day_val = m[day].as_long()
        start_val = m[start].as_long()
        
        # Map day to name
        days = ['Monday', 'Tuesday', 'Wednesday']
        day_name = days[day_val]
        
        # Convert start_val to time (HH:MM:HH:MM)
        start_h = 9 + (start_val // 60)
        start_m = start_val % 60
        end_val = start_val + 30
        end_h = 9 + (end_val // 60)
        end_m = end_val % 60
        
        time_str = f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}"
        print(f"{day_name} {time_str}")
    else:
        print("No solution")

schedule_meeting()