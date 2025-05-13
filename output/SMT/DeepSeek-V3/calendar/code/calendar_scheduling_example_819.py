from z3 import *

def find_meeting_time():
    # Initialize the solver with optimization
    opt = Optimize()
    
    # Meeting duration is 30 minutes
    meeting_duration = 30
    
    # Work hours are from 9:00 to 17:00 (480 minutes total, from 0 to 480)
    start_time = 0  # 9:00 AM as 0 minutes
    end_time = 480   # 17:00 PM as 480 minutes (8 hours * 60 minutes)
    
    # Define the meeting start time and day
    meeting_start = Int('meeting_start')
    meeting_day = Int('meeting_day')  # 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday
    
    # Day must be one of the four options
    opt.add(Or(meeting_day == 0, meeting_day == 1, meeting_day == 2, meeting_day == 3))
    
    # Meeting must be within work hours
    opt.add(meeting_start >= start_time)
    opt.add(meeting_start + meeting_duration <= end_time)
    
    # Julie is free all week (no constraints)
    
    # Ruth's busy slots
    ruth_busy = {
        0: [(9*60, 17*60)],  # Monday (all day)
        1: [(9*60, 17*60)],  # Tuesday (all day)
        2: [(9*60, 17*60)],  # Wednesday (all day)
        3: [(9*60, 11*60),   # Thursday
            (11*60+30, 14*60+30),
            (15*60, 17*60)]
    }
    
    # Julie's preference: avoid Thursday before 11:30
    # We'll model this as a soft constraint with penalty
    penalty = Int('penalty')
    opt.add(penalty >= 0)
    thursday_early_penalty = If(And(meeting_day == 3, meeting_start < (11*60+30)), 100, 0)
    opt.add(penalty == thursday_early_penalty)
    
    # Function to add no-overlap constraints
    def add_busy_constraints(day, busy_slots):
        for slot_start, slot_end in busy_slots:
            opt.add(Implies(meeting_day == day,
                          Or(meeting_start + meeting_duration <= slot_start,
                             meeting_start >= slot_end)))
    
    # Add constraints for Ruth's busy times
    for day in [0, 1, 2, 3]:
        add_busy_constraints(day, ruth_busy[day])
    
    # We want to minimize the penalty (prefer not Thursday before 11:30)
    opt.minimize(penalty)
    
    # Also prefer earlier times among equally preferred options
    opt.minimize(meeting_start)
    
    # Check for solution
    if opt.check() == sat:
        m = opt.model()
        day = m[meeting_day].as_long()
        start_min = m[meeting_start].as_long()
        
        # Convert to readable time
        days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
        hours = 9 + start_min // 60
        minutes = start_min % 60
        end_min = start_min + meeting_duration
        end_h = 9 + end_min // 60
        end_m = end_min % 60
        
        print(f"Optimal meeting time: {days[day]} {hours:02d}:{minutes:02d}-{end_h:02d}:{end_m:02d}")
    else:
        print("No suitable time slot found")

find_meeting_time()