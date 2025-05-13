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
    
    # Participants' busy slots (day: list of (start, end) in minutes from 9:00)
    nicole_busy = {
        0: [(9*60, 9*60+30), (13*60, 13*60+30), (14*60+30, 15*60+30)],  # Monday
        1: [(9*60, 9*60+30), (11*60+30, 13*60+30), (14*60+30, 15*60+30)],  # Tuesday
        2: [(10*60, 11*60), (12*60+30, 15*60), (16*60, 17*60)]  # Wednesday
    }
    
    ruth_busy = {
        0: [(9*60, 17*60)],  # Monday (entire day)
        1: [(9*60, 17*60)],  # Tuesday (entire day)
        2: [(9*60, 10*60+30), (11*60, 11*60+30), (12*60, 12*60+30), 
            (13*60+30, 15*60+30), (16*60, 16*60+30)]  # Wednesday
    }
    
    # Ruth's constraint: cannot meet on Wednesday after 13:30 (13*60+30)
    opt.add(Implies(meeting_day == 2, meeting_start + meeting_duration <= 13*60+30))
    
    # Function to add no-overlap constraints
    def add_busy_constraints(day, busy_slots):
        for slot_start, slot_end in busy_slots:
            opt.add(Implies(meeting_day == day,
                          Or(meeting_start + meeting_duration <= slot_start,
                             meeting_start >= slot_end)))
    
    # Add constraints for both participants
    for day in [0, 1, 2]:
        add_busy_constraints(day, nicole_busy.get(day, []))
        add_busy_constraints(day, ruth_busy.get(day, []))
    
    # To find the earliest possible time, we'll minimize the start time
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