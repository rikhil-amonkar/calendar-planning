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
    meeting_day = Int('meeting_day')  # 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday
    
    # Day must be one of the five options
    opt.add(Or(meeting_day == 0, meeting_day == 1, meeting_day == 2, meeting_day == 3, meeting_day == 4))
    
    # Meeting must be within work hours
    opt.add(meeting_start >= start_time)
    opt.add(meeting_start + meeting_duration <= end_time)
    
    # Daniel's preferences (avoid Wednesday and Thursday)
    opt.add(meeting_day != 2)  # Wednesday
    opt.add(meeting_day != 3)  # Thursday
    
    # Bradley's preferences (avoid Monday, Tuesday before 12:00, and Friday)
    opt.add(meeting_day != 0)  # Monday
    opt.add(Implies(meeting_day == 1, meeting_start >= 12*60))  # Tuesday after 12:00
    opt.add(meeting_day != 4)  # Friday
    
    # Daniel's busy slots (day: list of (start, end) in minutes from 9:00)
    daniel_busy = {
        0: [(9*60+30, 10*60+30), (12*60, 12*60+30), (13*60, 14*60), (14*60+30, 15*60), (15*60+30, 16*60)],  # Monday
        1: [(11*60, 12*60), (13*60, 13*60+30), (15*60+30, 16*60), (16*60+30, 17*60)],  # Tuesday
        2: [(9*60, 10*60), (14*60, 14*60+30)],  # Wednesday
        3: [(10*60+30, 11*60), (12*60, 13*60), (14*60+30, 15*60), (15*60+30, 16*60)],  # Thursday
        4: [(9*60, 9*60+30), (11*60+30, 12*60), (13*60, 13*60+30), (16*60+30, 17*60)]  # Friday
    }
    
    # Bradley's busy slots (day: list of (start, end) in minutes from 9:00)
    bradley_busy = {
        0: [(9*60+30, 11*60), (11*60+30, 12*60), (12*60+30, 13*60), (14*60, 15*60)],  # Monday
        1: [(10*60+30, 11*60), (12*60, 13*60), (13*60+30, 14*60), (15*60+30, 16*60+30)],  # Tuesday
        2: [(9*60, 10*60), (11*60, 13*60), (13*60+30, 14*60), (14*60+30, 17*60)],  # Wednesday
        3: [(9*60, 12*60+30), (13*60+30, 14*60), (14*60+30, 15*60), (15*60+30, 16*60+30)],  # Thursday
        4: [(9*60, 9*60+30), (10*60, 12*60+30), (13*60, 13*60+30), (14*60, 14*60+30), (15*60+30, 16*60+30)]  # Friday
    }
    
    # Function to add no-overlap constraints
    def add_busy_constraints(day, busy_slots):
        for slot_start, slot_end in busy_slots:
            opt.add(Implies(meeting_day == day,
                          Or(meeting_start + meeting_duration <= slot_start,
                             meeting_start >= slot_end)))
    
    # Add constraints for Daniel and Bradley for each day
    for day in [0, 1, 2, 3, 4]:
        add_busy_constraints(day, daniel_busy.get(day, []))
        add_busy_constraints(day, bradley_busy.get(day, []))
    
    # To find the earliest possible time, we'll minimize the start time
    opt.minimize(meeting_start)
    
    # Check for solution
    if opt.check() == sat:
        m = opt.model()
        day = m[meeting_day].as_long()
        start_min = m[meeting_start].as_long()
        
        # Convert to readable time
        days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
        hours = 9 + start_min // 60
        minutes = start_min % 60
        end_min = start_min + meeting_duration
        end_h = 9 + end_min // 60
        end_m = end_min % 60
        
        print(f"Optimal meeting time: {days[day]} {hours:02d}:{minutes:02d}-{end_h:02d}:{end_m:02d}")
    else:
        print("No suitable time slot found")

find_meeting_time()