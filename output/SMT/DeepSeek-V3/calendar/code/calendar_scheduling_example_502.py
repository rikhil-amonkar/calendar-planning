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
    
    # Constraints for the meeting start time
    s.add(meeting_start >= start_time)
    s.add(meeting_start + meeting_duration <= end_time)
    
    # Jack's busy slots (in minutes from 9:00 AM)
    jack_busy = [
        (9 * 60 + 30 - 9 * 60, 10 * 60 + 30 - 9 * 60),  # 9:30-10:30
        (11 * 60 - 9 * 60, 11 * 60 + 30 - 9 * 60),      # 11:00-11:30
        (12 * 60 + 30 - 9 * 60, 13 * 60 - 9 * 60),      # 12:30-13:00
        (14 * 60 - 9 * 60, 14 * 60 + 30 - 9 * 60),      # 14:00-14:30
        (16 * 60 - 9 * 60, 16 * 60 + 30 - 9 * 60)        # 16:00-16:30
    ]
    
    # Charlotte's busy slots (in minutes from 9:00 AM)
    charlotte_busy = [
        (9 * 60 + 30 - 9 * 60, 10 * 60 - 9 * 60),       # 9:30-10:00
        (10 * 60 + 30 - 9 * 60, 12 * 60 - 9 * 60),       # 10:30-12:00
        (12 * 60 + 30 - 9 * 60, 13 * 60 + 30 - 9 * 60), # 12:30-13:30
        (14 * 60 - 9 * 60, 16 * 60 - 9 * 60)            # 14:00-16:00
    ]
    
    # Jack's preference: avoid meetings after 12:30
    # We'll model this as a soft constraint with a penalty
    penalty = Int('penalty')
    s.add(penalty >= 0)
    
    # Penalty for scheduling after 12:30 (12:30 = 210 minutes from 9:00)
    after_1230_penalty = If(meeting_start >= (12 * 60 + 30 - 9 * 60), 100, 0)
    s.add(penalty == after_1230_penalty)
    
    # Function to add constraints that the meeting does not overlap with busy slots
    def add_no_overlap_constraints(busy_slots):
        for slot_start, slot_end in busy_slots:
            s.add(Or(
                meeting_start + meeting_duration <= slot_start,
                meeting_start >= slot_end
            ))
    
    # Add constraints for both participants
    add_no_overlap_constraints(jack_busy)
    add_no_overlap_constraints(charlotte_busy)
    
    # We want to minimize the penalty (prefer times before 12:30)
    opt = Optimize()
    opt.add(s.assertions())
    opt.minimize(penalty)
    
    # Check if there's a solution
    if opt.check() == sat:
        m = opt.model()
        start_minutes = m[meeting_start].as_long()
        
        # Convert minutes back to time format
        hours = 9 + start_minutes // 60
        minutes = start_minutes % 60
        end_minutes = start_minutes + meeting_duration
        end_hours = 9 + end_minutes // 60
        end_minutes = end_minutes % 60
        
        print(f"Meeting can be scheduled from {hours:02d}:{minutes:02d} to {end_hours:02d}:{end_minutes:02d}")
    else:
        print("No suitable time slot found.")

find_meeting_time()