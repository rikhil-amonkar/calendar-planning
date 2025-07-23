def find_meeting_time():
    # Define work hours and days to consider
    work_hours_start = 9 * 60  # 9:00 in minutes
    work_hours_end = 17 * 60    # 17:00 in minutes
    days = ['Monday', 'Tuesday', 'Wednesday']
    
    # Samuel's busy times in minutes since midnight for each day
    samuel_busy = {
        'Monday': [(10*60 + 30, 11*60), (12*60, 12*60 + 30), (13*60, 15*60), (15*60 + 30, 16*60 + 30)],
        'Tuesday': [(9*60, 12*60), (14*60, 15*60 + 30), (16*60 + 30, 17*60)],
        'Wednesday': [(10*60 + 30, 11*60), (11*60 + 30, 12*60), (12*60 + 30, 13*60), (14*60, 14*60 + 30), (15*60, 16*60)]
    }
    
    # Preferences: Larry doesn't want Wednesday, Samuel wants to avoid Tuesday
    preferred_days = ['Monday', 'Tuesday']  # Exclude Wednesday first
    
    meeting_duration = 30  # minutes
    
    # Check Monday first (preferred by both)
    for day in preferred_days + ['Wednesday']:
        if day == 'Tuesday' and day in preferred_days:
            # Samuel wants to avoid Tuesday, so only check if no other option
            continue
        
        # Get Samuel's busy times for the day
        busy_times = samuel_busy.get(day, [])
        
        # Generate available slots
        available_slots = []
        prev_end = work_hours_start
        
        for start, end in sorted(busy_times):
            if start > prev_end:
                available_slots.append((prev_end, start))
            prev_end = max(prev_end, end)
        
        # Check after the last meeting
        if prev_end < work_hours_end:
            available_slots.append((prev_end, work_hours_end))
        
        # Find the earliest available slot that fits the meeting duration
        for slot in available_slots:
            slot_start, slot_end = slot
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
    
    # If no slot found in preferred days, check Wednesday (even though Larry doesn't prefer it)
    day = 'Wednesday'
    busy_times = samuel_busy.get(day, [])
    available_slots = []
    prev_end = work_hours_start
    
    for start, end in sorted(busy_times):
        if start > prev_end:
            available_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    
    if prev_end < work_hours_end:
        available_slots.append((prev_end, work_hours_end))
    
    for slot in available_slots:
        slot_start, slot_end = slot
        if slot_end - slot_start >= meeting_duration:
            meeting_start = slot_start
            meeting_end = meeting_start + meeting_duration
            
            start_hh = meeting_start // 60
            start_mm = meeting_start % 60
            end_hh = meeting_end // 60
            end_mm = meeting_end % 60
            
            time_str = f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}"
            return day, time_str
    
    return None, None

day, time_str = find_meeting_time()
print(f"{day}, {time_str}")