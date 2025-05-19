def find_meeting_time():
    # Define work hours and constraints
    work_start = 9 * 60
    work_end = 17 * 60
    meeting_duration = 60
    day = "Monday"
    
    # Convert schedules to minutes since midnight
    schedules = {
        'Anthony': [(9*60+30, 10*60), (12*60, 13*60), (16*60, 16*60+30)],
        'Pamela': [(9*60+30, 10*60), (16*60+30, 17*60)],
        'Zachary': [(9*60, 11*60+30), (12*60, 12*60+30), (13*60, 13*60+30), (14*60+30, 15*60), (16*60, 17*60)],
    }
    
    # Pamela's time restriction (meeting must end by 14:30)
    max_end = 14 * 60 + 30
    
    # Find available slots for all participants
    for start in range(work_start, max_end - meeting_duration + 1):
        end = start + meeting_duration
        if end > max_end:
            continue
        
        # Check all participants' availability
        valid = True
        for person, busy in schedules.items():
            for s, e in busy:
                if not (end <= s or start >= e):
                    valid = False
                    break
            if not valid:
                break
        
        if valid:
            # Format time to HH:MM
            return f"{day} {start//60:02d}:{start%60:02d}-{end//60:02d}:{end%60:02d}"
    
    return "No suitable time found"

result = find_meeting_time()
print(result)