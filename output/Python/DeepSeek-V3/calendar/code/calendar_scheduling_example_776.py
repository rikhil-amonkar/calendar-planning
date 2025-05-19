def find_meeting_time():
    # Define work hours and days to consider
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    days = ['Monday', 'Tuesday', 'Wednesday']
    
    # Define participants' schedules and constraints
    john_schedule = {
        'Monday': [],
        'Tuesday': [],
        'Wednesday': []
    }
    
    jennifer_schedule = {
        'Monday': [(9*60, 11*60), (11*60 + 30, 13*60), (13*60 + 30, 14*60 + 30), (15*60, 17*60)],
        'Tuesday': [(9*60, 11*60 + 30), (12*60, 17*60)],
        'Wednesday': [(9*60, 11*60 + 30), (12*60, 12*60 + 30), (13*60, 14*60), (14*60 + 30, 16*60), (16*60 + 30, 17*60)]
    }
    
    # John's constraints: avoid Monday after 14:30, avoid Tuesday and Wednesday
    john_constraints = {
        'Monday': (work_start, 14*60 + 30),
        'Tuesday': None,  # No available time due to constraint
        'Wednesday': None  # No available time due to constraint
    }
    
    meeting_duration = 30  # minutes
    
    # Iterate through each day to find a suitable time
    for day in days:
        if john_constraints[day] is None:
            continue  # Skip days John cannot attend
        
        # Get John's available time for the day
        john_available_start, john_available_end = john_constraints[day]
        
        # Get Jennifer's busy times for the day
        jennifer_busy = jennifer_schedule[day]
        
        # Find Jennifer's free slots within work hours
        jennifer_free = []
        prev_end = work_start
        for start, end in sorted(jennifer_busy):
            if start > prev_end:
                jennifer_free.append((prev_end, start))
            prev_end = max(prev_end, end)
        if prev_end < work_end:
            jennifer_free.append((prev_end, work_end))
        
        # Find overlapping slots between John and Jennifer
        for j_start, j_end in jennifer_free:
            # Intersect with John's available time
            slot_start = max(j_start, john_available_start)
            slot_end = min(j_end, john_available_end)
            
            if slot_end - slot_start >= meeting_duration:
                # Found a suitable slot
                meeting_start = slot_start
                meeting_end = meeting_start + meeting_duration
                
                # Convert minutes back to HH:MM format
                def format_time(minutes):
                    hours = minutes // 60
                    mins = minutes % 60
                    return f"{hours:02d}:{mins:02d}"
                
                time_range = f"{format_time(meeting_start)}:{format_time(meeting_end)}"
                return day, time_range
    
    return None, None  # No suitable time found (though problem states there is one)

day, time_range = find_meeting_time()
print(f"{day}: {time_range}")