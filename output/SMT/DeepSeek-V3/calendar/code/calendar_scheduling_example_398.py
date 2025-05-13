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
    
    # Define busy slots for each participant (in minutes from 9:00 AM)
    busy_slots = {
        'Doris': [
            (9 * 60 - 9 * 60, 11 * 60 - 9 * 60),       # 9:00-11:00
            (13 * 60 + 30 - 9 * 60, 14 * 60 - 9 * 60),  # 13:30-14:00
            (16 * 60 - 9 * 60, 16 * 60 + 30 - 9 * 60)   # 16:00-16:30
        ],
        'Theresa': [
            (10 * 60 - 9 * 60, 12 * 60 - 9 * 60)       # 10:00-12:00
        ],
        'Christian': [],  # Free all day
        'Terry': [
            (9 * 60 + 30 - 9 * 60, 10 * 60 - 9 * 60),  # 9:30-10:00
            (11 * 60 + 30 - 9 * 60, 12 * 60 - 9 * 60),  # 11:30-12:00
            (12 * 60 + 30 - 9 * 60, 13 * 60 - 9 * 60),  # 12:30-13:00
            (13 * 60 + 30 - 9 * 60, 14 * 60 - 9 * 60),  # 13:30-14:00
            (14 * 60 + 30 - 9 * 60, 15 * 60 - 9 * 60),  # 14:30-15:00
            (15 * 60 + 30 - 9 * 60, 17 * 60 - 9 * 60)   # 15:30-17:00
        ],
        'Carolyn': [
            (9 * 60 - 9 * 60, 10 * 60 + 30 - 9 * 60),  # 9:00-10:30
            (11 * 60 - 9 * 60, 11 * 60 + 30 - 9 * 60),  # 11:00-11:30
            (12 * 60 - 9 * 60, 13 * 60 - 9 * 60),       # 12:00-13:00
            (13 * 60 + 30 - 9 * 60, 14 * 60 + 30 - 9 * 60),  # 13:30-14:30
            (15 * 60 - 9 * 60, 17 * 60 - 9 * 60)        # 15:00-17:00
        ],
        'Kyle': [
            (9 * 60 - 9 * 60, 9 * 60 + 30 - 9 * 60),    # 9:00-9:30
            (11 * 60 + 30 - 9 * 60, 12 * 60 - 9 * 60),   # 11:30-12:00
            (12 * 60 + 30 - 9 * 60, 13 * 60 - 9 * 60),   # 12:30-13:00
            (14 * 60 + 30 - 9 * 60, 17 * 60 - 9 * 60)    # 14:30-17:00
        ]
    }
    
    # Function to add constraints that the meeting does not overlap with busy slots
    def add_no_overlap_constraints(slots):
        for slot_start, slot_end in slots:
            s.add(Or(
                meeting_start + meeting_duration <= slot_start,
                meeting_start >= slot_end
            ))
    
    # Add constraints for each participant
    for participant, slots in busy_slots.items():
        add_no_overlap_constraints(slots)
    
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