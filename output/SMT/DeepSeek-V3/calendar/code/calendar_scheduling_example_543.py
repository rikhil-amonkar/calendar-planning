from z3 import *

def find_meeting_time():
    # Initialize the solver
    s = Solver()
    
    # Meeting duration is 1 hour (60 minutes)
    meeting_duration = 60
    
    # Work hours are from 9:00 to 17:00 (480 minutes total, from 0 to 480)
    start_time = 0  # 9:00 AM as 0 minutes
    end_time = 480   # 17:00 PM as 480 minutes (8 hours * 60 minutes)
    
    # Define the start time of the meeting as a Z3 variable
    meeting_start = Int('meeting_start')
    
    # Constraints for the meeting start time
    s.add(meeting_start >= start_time)
    s.add(meeting_start + meeting_duration <= end_time)
    
    # James's busy slots (in minutes from 9:00 AM)
    james_busy = [
        (11 * 60 + 30 - 9 * 60, 12 * 60 - 9 * 60),       # 11:30-12:00 (30 minutes)
        (14 * 60 + 30 - 9 * 60, 15 * 60 - 9 * 60)        # 14:30-15:00 (30 minutes)
    ]
    
    # John's busy slots (in minutes from 9:00 AM)
    john_busy = [
        (9 * 60 + 30 - 9 * 60, 11 * 60 - 9 * 60),        # 9:30-11:00 (90 minutes)
        (11 * 60 + 30 - 9 * 60, 12 * 60 - 9 * 60),       # 11:30-12:00 (30 minutes)
        (12 * 60 + 30 - 9 * 60, 13 * 60 + 30 - 9 * 60),  # 12:30-13:30 (60 minutes)
        (14 * 60 + 30 - 9 * 60, 16 * 60 + 30 - 9 * 60)   # 14:30-16:30 (120 minutes)
    ]
    
    # Function to add constraints that the meeting does not overlap with busy slots
    def add_no_overlap_constraints(busy_slots):
        for slot_start, slot_end in busy_slots:
            s.add(Or(
                meeting_start + meeting_duration <= slot_start,
                meeting_start >= slot_end
            ))
    
    # Add constraints for James and John
    add_no_overlap_constraints(james_busy)
    add_no_overlap_constraints(john_busy)
    
    # Check if there's a solution
    if s.check() == sat:
        m = s.model()
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