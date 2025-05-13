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
    
    # Day must be one of the three options
    opt.add(Or(meeting_day == 0, meeting_day == 1, meeting_day == 2))
    
    # Meeting must be within work hours
    opt.add(meeting_start >= start_time)
    opt.add(meeting_start + meeting_duration <= end_time)
    
    # Nancy's busy slots (day: list of (start, end) in minutes from 9:00)
    nancy_busy = {
        0: [(10*60, 10*60+30), (11*60+30, 12*60+30), (13*60+30, 14*60), 
            (14*60+30, 15*60+30), (16*60, 17*60)],
        1: [(9*60+30, 10*60+30), (11*60, 11*60+30), (12*60, 12*60+30),
            (13*60, 13*60+30), (15*60+30, 16*60)],
        2: [(10*60, 11*60+30), (13*60+30, 16*60)]
    }
    
    # Jose's busy slots
    jose_busy = {
        0: [(9*60, 17*60)],  # Entire Monday
        1: [(9*60, 17*60)],  # Entire Tuesday
        2: [(9*60, 9*60+30), (10*60, 12*60+30), 
            (13*60+30, 14*60+30), (15*60, 17*60)]
    }
    
    # Function to add no-overlap constraints
    def add_busy_constraints(busy_slots, day):
        for slot_start, slot_end in busy_slots[day]:
            opt.add(Or(
                meeting_start + meeting_duration <= slot_start,
                meeting_start >= slot_end
            ))
    
    # Add constraints for each possible day
    for day in [0, 1, 2]:
        # Only apply constraints if meeting is on this day
        opt.add(Implies(meeting_day == day,
                      And(
                          # Nancy's availability
                          *[Or(meeting_start + meeting_duration <= slot_start,
                               meeting_start >= slot_end)
                           for slot_start, slot_end in nancy_busy[day]],
                          # Jose's availability
                          *[Or(meeting_start + meeting_duration <= slot_start,
                               meeting_start >= slot_end)
                           for slot_start, slot_end in jose_busy[day]]
                      )))
    
    # To find earliest availability, minimize: (day * 1000 + start_time)
    # This ensures we get earliest day first, then earliest time that day
    time_score = meeting_day * 1000 + meeting_start
    opt.minimize(time_score)
    
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
        
        print(f"Earliest meeting time: {days[day]} {hours:02d}:{minutes:02d}-{end_h:02d}:{end_m:02d}")
    else:
        print("No suitable time slot found")

find_meeting_time()