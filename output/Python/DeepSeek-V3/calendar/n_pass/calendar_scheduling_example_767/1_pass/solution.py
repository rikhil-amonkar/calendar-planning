def find_meeting_time():
    # Define work hours and days to consider
    work_hours_start = 9 * 60  # 9:00 in minutes
    work_hours_end = 17 * 60    # 17:00 in minutes
    days = ['Monday', 'Tuesday', 'Wednesday']
    
    # Define blocked times for each participant in minutes since midnight
    martha_blocked = {
        'Monday': [(16 * 60, 17 * 60)],
        'Tuesday': [(15 * 60, 15 * 60 + 30)],
        'Wednesday': [(10 * 60, 11 * 60), (14 * 60, 14 * 60 + 30)]
    }
    
    beverly_blocked = {
        'Monday': [(9 * 60, 13 * 60 + 30), (14 * 60, 17 * 60)],
        'Tuesday': [(9 * 60, 17 * 60)],
        'Wednesday': [(9 * 60 + 30, 15 * 60 + 30), (16 * 60 + 30, 17 * 60)]
    }
    
    meeting_duration = 60  # minutes
    
    for day in days:
        # Combine and sort all blocked times for the day
        all_blocked = []
        if day in martha_blocked:
            all_blocked.extend(martha_blocked[day])
        if day in beverly_blocked:
            all_blocked.extend(beverly_blocked[day])
        all_blocked.sort()
        
        # Find available slots
        available_start = work_hours_start
        available_slots = []
        
        for block_start, block_end in all_blocked:
            if block_start > available_start:
                available_slots.append((available_start, block_start))
            available_start = max(available_start, block_end)
        
        if available_start < work_hours_end:
            available_slots.append((available_start, work_hours_end))
        
        # Check each available slot for a meeting
        for slot_start, slot_end in available_slots:
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