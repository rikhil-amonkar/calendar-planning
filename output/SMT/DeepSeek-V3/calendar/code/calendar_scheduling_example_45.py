from z3 import *

def find_meeting_time():
    # Initialize the solver with optimization
    opt = Optimize()
    
    # Meeting duration is 30 minutes
    meeting_duration = 30
    
    # Work hours are from 9:00 to 17:00 (480 minutes total, from 0 to 480)
    start_time = 0  # 9:00 AM as 0 minutes
    end_time = 480   # 17:00 PM as 480 minutes (8 hours * 60 minutes)
    
    # Define the meeting start time
    meeting_start = Int('meeting_start')
    
    # Meeting must be within work hours
    opt.add(meeting_start >= start_time)
    opt.add(meeting_start + meeting_duration <= end_time)
    
    # Participants' busy slots (in minutes from 9:00)
    # Andrew is free all day (no constraints)
    # Grace is free all day (no constraints)
    
    samuel_busy = [
        (9*60, 10*60+30),   # 9:00-10:30
        (11*60+30, 12*60),   # 11:30-12:00
        (13*60, 13*60+30),   # 13:00-13:30
        (14*60, 16*60),      # 14:00-16:00
        (16*60+30, 17*60)    # 16:30-17:00
    ]
    
    # Function to add no-overlap constraints
    def add_busy_constraints(busy_slots):
        for slot_start, slot_end in busy_slots:
            opt.add(Or(
                meeting_start + meeting_duration <= slot_start,
                meeting_start >= slot_end
            ))
    
    # Add constraints for Samuel
    add_busy_constraints(samuel_busy)
    
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
        
        print(f"Earliest available meeting time: {hours:02d}:{minutes:02d}-{end_h:02d}:{end_m:02d}")
    else:
        print("No suitable time slot found")

find_meeting_time()