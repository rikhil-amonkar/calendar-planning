def find_meeting_time():
    # Define work hours and days
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
    
    # Define schedules in minutes since midnight
    bryan_busy = {
        'Thursday': [(9*60+30, 10*60), (12*60+30, 13*60)],
        'Friday': [(10*60+30, 11*60), (14*60, 14*60+30)]
    }
    
    nicholas_busy = {
        'Monday': [(11*60+30, 12*60), (13*60, 15*60+30)],
        'Tuesday': [(9*60, 9*60+30), (11*60, 13*60+30), (14*60, 16*60+30)],
        'Wednesday': [(9*60, 9*60+30), (10*60, 11*60), (11*60+30, 13*60+30), 
                     (14*60, 14*60+30), (15*60, 16*60+30)],
        'Thursday': [(10*60+30, 11*60+30), (12*60, 12*60+30), 
                    (15*60, 15*60+30), (16*60+30, 17*60)],
        'Friday': [(9*60, 10*60+30), (11*60, 12*60), (12*60+30, 14*60+30),
                  (15*60+30, 16*60), (16*60+30, 17*60)]
    }
    
    # Preferred day constraints
    preferred_days = ['Wednesday', 'Friday']  # Exclude Tuesday (Bryan) and Monday/Thursday (Nicholas)
    
    for day in preferred_days:
        # Get busy times for both participants
        bryan_day = bryan_busy.get(day, [])
        nicholas_day = nicholas_busy.get(day, [])
        
        # Combine and sort all busy intervals
        all_busy = sorted(bryan_day + nicholas_day, key=lambda x: x[0])
        
        # Find free slots
        current_time = work_start
        for start, end in all_busy:
            if current_time < start:
                free_slot = (current_time, start)
                if free_slot[1] - free_slot[0] >= 60:  # Check if slot can fit 1 hour
                    return format_time(free_slot[0], free_slot[1], day)
            current_time = max(current_time, end)
        
        # Check after last meeting
        if current_time < work_end:
            if work_end - current_time >= 60:
                return format_time(current_time, current_time + 60, day)
    
    return "No suitable time found"

def format_time(start, end, day):
    def to_hhmm(minutes):
        return f"{minutes//60:02}:{minutes%60:02}"
    return f"{day} {to_hhmm(start)}:{to_hhmm(end)}"

print(find_meeting_time())