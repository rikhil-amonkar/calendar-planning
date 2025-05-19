def find_meeting_time():
    # Define work hours and days
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
    
    # Define busy times for Nicole and Daniel in minutes since midnight
    nicole_busy = {
        'Tuesday': [(16 * 60, 16 * 60 + 30)],
        'Wednesday': [(15 * 60, 15 * 60 + 30)],
        'Friday': [(12 * 60, 12 * 60 + 30), (15 * 60 + 30, 16 * 60)]
    }
    
    daniel_busy = {
        'Monday': [(9 * 60, 12 * 60 + 30), (13 * 60, 13 * 60 + 30), (14 * 60, 16 * 60 + 30)],
        'Tuesday': [(9 * 60, 10 * 60 + 30), (11 * 60 + 30, 12 * 60 + 30), (13 * 60, 13 * 60 + 30), 
                    (15 * 60, 16 * 60), (16 * 60 + 30, 17 * 60)],
        'Wednesday': [(9 * 60, 10 * 60), (11 * 60, 12 * 60 + 30), (13 * 60, 13 * 60 + 30), 
                      (14 * 60, 14 * 60 + 30), (16 * 60 + 30, 17 * 60)],
        'Thursday': [(11 * 60, 12 * 60), (13 * 60, 14 * 60), (15 * 60, 15 * 60 + 30)],
        'Friday': [(10 * 60, 11 * 60), (11 * 60 + 30, 12 * 60), (12 * 60 + 30, 14 * 60 + 30), 
                   (15 * 60, 15 * 60 + 30), (16 * 60, 16 * 60 + 30)]
    }
    
    meeting_duration = 60  # 1 hour in minutes
    
    for day in days:
        # Collect all busy intervals for the day
        busy_intervals = []
        
        # Add Nicole's busy times
        if day in nicole_busy:
            busy_intervals.extend(nicole_busy[day])
        
        # Add Daniel's busy times
        if day in daniel_busy:
            busy_intervals.extend(daniel_busy[day])
        
        # Sort busy intervals by start time
        busy_intervals.sort()
        
        # Find free slots
        prev_end = work_start
        free_slots = []
        
        for start, end in busy_intervals:
            if start > prev_end:
                free_slots.append((prev_end, start))
            prev_end = max(prev_end, end)
        
        # Check after last busy interval
        if prev_end < work_end:
            free_slots.append((prev_end, work_end))
        
        # Find the first suitable slot
        for start, end in free_slots:
            if end - start >= meeting_duration:
                meeting_start = start
                meeting_end = meeting_start + meeting_duration
                # Format the time as HH:MM:HH:MM
                start_hh = meeting_start // 60
                start_mm = meeting_start % 60
                end_hh = meeting_end // 60
                end_mm = meeting_end % 60
                time_str = f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}"
                return day, time_str
    
    return None, None

day, time = find_meeting_time()
print(f"{day}, {time}")