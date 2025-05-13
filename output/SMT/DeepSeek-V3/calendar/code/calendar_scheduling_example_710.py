from z3 import *

def find_meeting_time():
    # Initialize the solver
    s = Solver()
    
    # Meeting duration is 30 minutes
    meeting_duration = 30
    
    # Work hours are from 9:00 to 17:00 (480 minutes total, from 0 to 480)
    start_time = 0  # 9:00 AM as 0 minutes
    end_time = 480   # 17:00 PM as 480 minutes (8 hours * 60 minutes)
    
    # Define the meeting start time and day
    meeting_start = Int('meeting_start')
    meeting_day = Int('meeting_day')  # 0=Monday, 1=Tuesday, 2=Wednesday
    
    # Day must be Monday (0) or Tuesday (1) - Cheryl can't meet on Wednesday
    s.add(Or(meeting_day == 0, meeting_day == 1))
    
    # Meeting must be within work hours
    s.add(meeting_start >= start_time)
    s.add(meeting_start + meeting_duration <= end_time)
    
    # Cheryl's busy slots (day: list of (start, end) in minutes from 9:00)
    cheryl_busy = {
        0: [(9*60, 9*60+30), (11*60+30, 13*60), (15*60+30, 16*60)],
        1: [(15*60, 15*60+30)]
    }
    
    # Kyle's busy slots
    kyle_busy = {
        0: [(9*60, 17*60)],  # Entire Monday
        1: [(9*60+30, 17*60)],  # From 9:30 onward on Tuesday
        2: [(9*60, 9*60+30), (10*60, 13*60), (13*60+30, 14*60), (14*60+30, 17*60)]
    }
    
    # Function to add no-overlap constraints
    def add_busy_constraints(day, busy_slots):
        for slot_start, slot_end in busy_slots:
            s.add(Implies(meeting_day == day,
                         Or(meeting_start + meeting_duration <= slot_start,
                            meeting_start >= slot_end)))
    
    # Add constraints for each participant
    for day in [0, 1]:  # Only Monday and Tuesday
        add_busy_constraints(day, cheryl_busy[day])
        add_busy_constraints(day, kyle_busy[day])
    
    # Check for solution
    if s.check() == sat:
        m = s.model()
        day = m[meeting_day].as_long()
        start_min = m[meeting_start].as_long()
        
        # Convert to readable time
        days = ["Monday", "Tuesday", "Wednesday"]
        hours = 9 + start_min // 60
        minutes = start_min % 60
        end_min = start_min + meeting_duration
        end_h = 9 + end_min // 60
        end_m = end_min % 60
        
        print(f"Meeting can be scheduled on {days[day]} from {hours:02d}:{minutes:02d} to {end_h:02d}:{end_m:02d}")
    else:
        print("No suitable time slot found")

find_meeting_time()