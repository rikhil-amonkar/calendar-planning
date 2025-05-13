from z3 import *

def find_meeting_time():
    # Initialize the solver
    s = Solver()
    
    # Meeting duration is 30 minutes
    meeting_duration = 30
    
    # Work hours are from 9:00 to 17:00 (480 minutes total, from 0 to 480)
    start_time = 0  # 9:00 AM as 0 minutes
    end_time = 480   # 17:00 PM as 480 minutes (8 hours * 60 minutes)
    
    # Define the start time of the meeting as a Z3 variable
    meeting_start = Int('meeting_start')
    # Define the day of the meeting (0 for Monday, 1 for Tuesday)
    meeting_day = Int('meeting_day')
    s.add(Or(meeting_day == 0, meeting_day == 1))
    
    # Jeffrey is free the entire week, so no constraints for him
    
    # Harold's busy slots (in minutes from 9:00 AM)
    harold_busy = {
        # Monday
        0: [
            (9 * 60 - 9 * 60, 10 * 60 - 9 * 60),       # 9:00-10:00
            (10 * 60 + 30 - 9 * 60, 17 * 60 - 9 * 60)   # 10:30-17:00
        ],
        # Tuesday
        1: [
            (9 * 60 - 9 * 60, 9 * 60 + 30 - 9 * 60),   # 9:00-9:30
            (10 * 60 + 30 - 9 * 60, 11 * 60 + 30 - 9 * 60),  # 10:30-11:30
            (12 * 60 + 30 - 9 * 60, 13 * 60 + 30 - 9 * 60),  # 12:30-13:30
            (14 * 60 + 30 - 9 * 60, 15 * 60 + 30 - 9 * 60),  # 14:30-15:30
            (16 * 60 - 9 * 60, 17 * 60 - 9 * 60)        # 16:00-17:00
        ]
    }
    
    # Harold's preferences:
    # 1. Avoid Monday if possible (add soft constraint)
    # 2. On Tuesday, prefer after 14:30 (add soft constraint)
    
    # Soft constraints (preferences)
    # We'll use a simple approach by adding a penalty for undesired times
    # and minimizing the total penalty
    
    # Define penalty variables
    penalty = Int('penalty')
    s.add(penalty >= 0)
    
    # Penalty for Monday: 100 (high penalty to avoid Monday)
    monday_penalty = If(meeting_day == 0, 100, 0)
    
    # Penalty for Tuesday before 14:30: 50
    tuesday_early_penalty = If(And(meeting_day == 1, meeting_start < (14 * 60 + 30 - 9 * 60)), 50, 0)
    
    # Total penalty
    s.add(penalty == monday_penalty + tuesday_early_penalty)
    
    # Main constraints
    # Meeting must fit within work hours
    s.add(meeting_start >= start_time)
    s.add(meeting_start + meeting_duration <= end_time)
    
    # Meeting must not overlap with Harold's busy slots
    for day, slots in harold_busy.items():
        for slot_start, slot_end in slots:
            s.add(Implies(meeting_day == day,
                         Or(meeting_start + meeting_duration <= slot_start,
                            meeting_start >= slot_end)))
    
    # We want to minimize the penalty
    opt = Optimize()
    opt.add(s.assertions())
    opt.minimize(penalty)
    
    # Check if there's a solution
    if opt.check() == sat:
        m = opt.model()
        start_minutes = m[meeting_start].as_long()
        day = m[meeting_day].as_long()
        
        # Convert minutes back to time format
        hours = 9 + start_minutes // 60
        minutes = start_minutes % 60
        end_minutes = start_minutes + meeting_duration
        end_hours = 9 + end_minutes // 60
        end_minutes = end_minutes % 60
        
        day_name = "Monday" if day == 0 else "Tuesday"
        print(f"Meeting can be scheduled on {day_name} from {hours:02d}:{minutes:02d} to {end_hours:02d}:{end_minutes:02d}")
    else:
        print("No suitable time slot found.")

find_meeting_time()