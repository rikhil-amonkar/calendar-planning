def find_meeting_time():
    # Define work hours and days
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    days = ['Monday', 'Tuesday', 'Wednesday']
    
    # Define busy slots for Robert and Ralph in minutes since midnight
    robert_busy = {
        'Monday': [(11 * 60, 11 * 60 + 30), (14 * 60, 14 * 60 + 30), (15 * 60 + 30, 16 * 60)],
        'Tuesday': [(10 * 60 + 30, 11 * 60), (15 * 60, 15 * 60 + 30)],
        'Wednesday': [(10 * 60, 11 * 60), (11 * 60 + 30, 12 * 60), (12 * 60 + 30, 13 * 60), 
                     (13 * 60 + 30, 14 * 60), (15 * 60, 15 * 60 + 30), (16 * 60, 16 * 60 + 30)]
    }
    
    ralph_busy = {
        'Monday': [(10 * 60, 13 * 60 + 30), (14 * 60, 14 * 60 + 30), (15 * 60, 17 * 60)],
        'Tuesday': [(9 * 60, 9 * 60 + 30), (10 * 60, 10 * 60 + 30), (11 * 60, 11 * 60 + 30), 
                    (12 * 60, 13 * 60), (14 * 60, 15 * 60 + 30), (16 * 60, 17 * 60)],
        'Wednesday': [(10 * 60 + 30, 11 * 60), (11 * 60 + 30, 12 * 60), (13 * 60, 14 * 60 + 30), 
                     (16 * 60 + 30, 17 * 60)]
    }
    
    meeting_duration = 30  # minutes
    
    # Iterate through days in order (Monday, Tuesday, Wednesday)
    for day in days:
        if day == 'Monday' and "Robert would like to avoid more meetings on Monday":
            continue  # Skip Monday as per Robert's preference
        
        # Combine and sort all busy slots for both participants
        all_busy = robert_busy.get(day, []) + ralph_busy.get(day, [])
        all_busy.sort()
        
        # Find free slots
        free_slots = []
        prev_end = work_start
        
        for start, end in all_busy:
            if start > prev_end:
                free_slots.append((prev_end, start))
            prev_end = max(prev_end, end)
        
        if prev_end < work_end:
            free_slots.append((prev_end, work_end))
        
        # Check each free slot for availability
        for slot_start, slot_end in free_slots:
            if slot_end - slot_start >= meeting_duration:
                meeting_start = slot_start
                meeting_end = meeting_start + meeting_duration
                # Format the time as HH:MM:HH:MM
                start_hh = meeting_start // 60
                start_mm = meeting_start % 60
                end_hh = meeting_end // 60
                end_mm = meeting_end % 60
                time_str = f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}"
                return day, time_str
    
    return None, None

day, time_str = find_meeting_time()
print(f"{day}: {time_str}")