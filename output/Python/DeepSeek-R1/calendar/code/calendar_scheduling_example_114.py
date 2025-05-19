def find_meeting_time():
    # Define work hours
    work_start = 9 * 60
    work_end = 17 * 60
    duration = 60

    # Convert schedules to minutes since midnight
    schedules = {
        "Stephanie": [(10*60, 10*60+30), (16*60, 16*60+30)],
        "Cheryl": [(10*60, 10*60+30), (11*60+30, 12*60), (13*60+30, 14*60), (16*60+30, 17*60)],
        "Bradley": [(9*60+30, 10*60), (10*60+30, 11*60+30), (13*60+30, 14*60), (14*60+30, 15*60), (15*60+30, 17*60)],
        "Steven": [(9*60, 12*60), (13*60, 13*60+30), (14*60+30, 17*60)]
    }

    # Create a timeline of available slots
    for minute in range(work_start, work_end - duration + 1):
        start = minute
        end = minute + duration
        available = True
        
        # Check all participants' schedules
        for person, busy in schedules.items():
            for s, e in busy:
                if not (end <= s or start >= e):
                    available = False
                    break
            if not available:
                break
        
        if available:
            # Convert back to HH:MM format
            def format_time(m):
                return f"{m//60:02d}:{m%60:02d}"
            
            return "Monday", (format_time(start), format_time(end))
    
    return None

meeting_day, (start, end) = find_meeting_time()
print(f"{meeting_day} {start}:{end}")