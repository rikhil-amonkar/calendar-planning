from z3 import *

def find_meeting_time():
    # Initialize the solver with optimization
    opt = Optimize()
    
    # Meeting duration is 30 minutes
    meeting_duration = 30
    
    # Work hours are from 9:00 to 17:00 (480 minutes total, from 0 to 480)
    start_time = 0   # 9:00 AM as 0 minutes
    end_time = 480    # 17:00 PM as 480 minutes (8 hours * 60 minutes)
    
    # Define the meeting start time
    meeting_start = Int('meeting_start')
    
    # Meeting must be within work hours
    opt.add(meeting_start >= start_time)
    opt.add(meeting_start + meeting_duration <= end_time)
    
    # Participants' busy slots (in minutes from 9:00)
    # Brandon is free all day (no constraints)
    john_busy = [
        (11*60+30, 12*60),    # 11:30-12:00
        (14*60, 14*60+30)      # 14:00-14:30
    ]
    
    megan_busy = [
        (12*60, 12*60+30),    # 12:00-12:30
        (14*60, 15*60),       # 14:00-15:00
        (15*60+30, 16*60)     # 15:30-16:00
    ]
    
    kimberly_busy = [
        (9*60, 9*60+30),      # 9:00-9:30
        (10*60, 10*60+30),     # 10:00-10:30
        (11*60, 14*60+30),     # 11:00-14:30
        (15*60, 16*60),        # 15:00-16:00
        (16*60+30, 17*60)      # 16:30-17:00
    ]
    
    sean_busy = [
        (10*60, 11*60),       # 10:00-11:00
        (11*60+30, 14*60),    # 11:30-14:00
        (15*60, 15*60+30)      # 15:00-15:30
    ]
    
    lori_busy = [
        (9*60, 9*60+30),      # 9:00-9:30
        (10*60+30, 12*60),    # 10:30-12:00
        (13*60, 14*60+30),    # 13:00-14:30
        (16*60, 16*60+30)      # 16:00-16:30
    ]
    
    # Function to add no-overlap constraints
    def add_busy_constraints(busy_slots):
        for slot_start, slot_end in busy_slots:
            opt.add(Or(
                meeting_start + meeting_duration <= slot_start,
                meeting_start >= slot_end
            ))
    
    # Add constraints for all participants except Brandon (who is free)
    add_busy_constraints(john_busy)
    add_busy_constraints(megan_busy)
    add_busy_constraints(kimberly_busy)
    add_busy_constraints(sean_busy)
    add_busy_constraints(lori_busy)
    
    # To find the earliest possible time, we'll minimize the start time
    opt.minimize(meeting_start)
    
    # Check for solution
    if opt.check() == sat:
        m = opt.model()
        start_min = m[meeting_start].as_long()
        
        # Convert to readable time
        hours = 9 + start_min // 60
        minutes = start_min % 60
        end_min = start_min + meeting_duration
        end_h = 9 + end_min // 60
        end_m = end_min % 60
        
        print(f"Optimal meeting time: {hours:02d}:{minutes:02d}-{end_h:02d}:{end_m:02d}")
    else:
        print("No suitable time slot found")

find_meeting_time()