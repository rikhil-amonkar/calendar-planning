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
    meeting_day = Int('meeting_day')  # 0=Monday, 1=Tuesday, 2=Wednesday
    
    # Ryan cannot meet on Wednesday (day 2)
    opt.add(meeting_day != 2)
    
    # Adam prefers to avoid Monday before 14:30 (14*60+30) and Tuesday
    # We'll implement this as soft constraints with penalties
    penalty = Int('penalty')
    opt.add(penalty >= 0)
    
    # Penalize Monday before 14:30 and all of Tuesday
    monday_penalty = If(And(meeting_day == 0, meeting_start < 14*60+30), 10, 0)
    tuesday_penalty = If(meeting_day == 1, 5, 0)  # Lower penalty for Tuesday than Monday morning
    opt.add(penalty == monday_penalty + tuesday_penalty)
    
    # Meeting must be within work hours
    opt.add(meeting_start >= start_time)
    opt.add(meeting_start + meeting_duration <= end_time)
    
    # Participants' busy slots (day: list of (start, end) in minutes from 9:00)
    ryan_busy = {
        0: [(9*60+30, 10*60), (11*60, 12*60), (13*60, 13*60+30), (15*60+30, 16*60)],  # Monday
        1: [(11*60+30, 12*60+30), (15*60+30, 16*60)],  # Tuesday
        2: [(12*60, 13*60), (15*60+30, 16*60), (16*60+30, 17*60)]  # Wednesday
    }
    
    adam_busy = {
        0: [(9*60, 10*60+30), (11*60, 13*60+30), (14*60, 16*60), (16*60+30, 17*60)],  # Monday
        1: [(9*60, 10*60), (10*60+30, 15*60+30), (16*60, 17*60)],  # Tuesday
        2: [(9*60, 9*60+30), (10*60, 11*60), (11*60+30, 14*60+30), (15*60, 15*60+30), (16*60, 16*60+30)]  # Wednesday
    }
    
    # Function to add no-overlap constraints
    def add_busy_constraints(day, busy_slots):
        for slot_start, slot_end in busy_slots:
            opt.add(Implies(meeting_day == day,
                          Or(meeting_start + meeting_duration <= slot_start,
                             meeting_start >= slot_end)))
    
    # Add constraints for each possible day (only Monday and Tuesday since Wednesday is excluded)
    for day in [0, 1]:
        add_busy_constraints(day, ryan_busy.get(day, []))
        add_busy_constraints(day, adam_busy.get(day, []))
    
    # We want to minimize the penalty (prefer times Adam prefers)
    opt.minimize(penalty)
    # Also prefer earlier times among equally preferred options
    opt.minimize(meeting_start)
    
    # Check for solution
    if opt.check() == sat:
        m = opt.model()
        day = m[meeting_day].as_long()
        start_min = m[meeting_start].as_long()
        
        # Convert to readable time
        days = ["Monday", "Tuesday", "Wednesday"]
        hours = 9 + start_min // 60
        minutes = start_min % 60
        end_min = start_min + meeting_duration
        end_h = 9 + end_min // 60
        end_m = end_min % 60
        
        print(f"Optimal meeting time: {days[day]} {hours:02d}:{minutes:02d}-{end_h:02d}:{end_m:02d}")
    else:
        print("No suitable time slot found")

find_meeting_time()