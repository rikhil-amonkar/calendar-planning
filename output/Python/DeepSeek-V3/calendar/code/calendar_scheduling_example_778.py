def find_meeting_time():
    # Define work hours and days to consider
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    days = ['Monday', 'Tuesday', 'Wednesday']
    
    # Define participants' schedules and constraints
    susan_schedule = {
        'Monday': [(12 * 60 + 30, 13 * 60), (13 * 60 + 30, 14 * 60)],
        'Tuesday': [(11 * 60 + 30, 12 * 60)],
        'Wednesday': [(9 * 60 + 30, 10 * 60 + 30), (14 * 60, 14 * 60 + 30), (15 * 60 + 30, 16 * 60 + 30)]
    }
    
    sandra_schedule = {
        'Monday': [(9 * 60, 13 * 60), (14 * 60, 15 * 60), (16 * 60, 16 * 60 + 30)],
        'Tuesday': [(9 * 60, 9 * 60 + 30), (10 * 60 + 30, 12 * 60), (12 * 60 + 30, 13 * 60 + 30), 
                    (14 * 60, 14 * 60 + 30), (16 * 60, 17 * 60)],
        'Wednesday': [(9 * 60, 11 * 60 + 30), (12 * 60, 12 * 60 + 30), (13 * 60, 17 * 60)]
    }
    
    # Susan prefers not to meet on Tuesday
    preferred_days = ['Monday', 'Wednesday']
    
    # Iterate through each day in preferred order
    for day in preferred_days:
        # Get both participants' busy times for the day
        susan_busy = susan_schedule.get(day, [])
        sandra_busy = sandra_schedule.get(day, [])
        
        # Combine and sort all busy intervals
        all_busy = susan_busy + sandra_busy
        all_busy.sort()
        
        # Find available slots
        available_slots = []
        prev_end = work_start
        
        for start, end in all_busy:
            if start > prev_end:
                available_slots.append((prev_end, start))
            prev_end = max(prev_end, end)
        
        # Check after last busy interval
        if prev_end < work_end:
            available_slots.append((prev_end, work_end))
        
        # Find first available 30-minute slot
        for slot_start, slot_end in available_slots:
            if slot_end - slot_start >= 30:
                meeting_start = slot_start
                meeting_end = meeting_start + 30
                # Format the time as HH:MM:HH:MM
                start_hh = meeting_start // 60
                start_mm = meeting_start % 60
                end_hh = meeting_end // 60
                end_mm = meeting_end % 60
                time_str = f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}"
                return day, time_str
    
    # If no slot found in preferred days, check Tuesday (though Susan prefers not)
    day = 'Tuesday'
    susan_busy = susan_schedule.get(day, [])
    sandra_busy = sandra_schedule.get(day, [])
    all_busy = susan_busy + sandra_busy
    all_busy.sort()
    
    available_slots = []
    prev_end = work_start
    
    for start, end in all_busy:
        if start > prev_end:
            available_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    
    if prev_end < work_end:
        available_slots.append((prev_end, work_end))
    
    for slot_start, slot_end in available_slots:
        if slot_end - slot_start >= 30:
            meeting_start = slot_start
            meeting_end = meeting_start + 30
            start_hh = meeting_start // 60
            start_mm = meeting_start % 60
            end_hh = meeting_end // 60
            end_mm = meeting_end % 60
            time_str = f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}"
            return day, time_str
    
    return None, None

day, time_slot = find_meeting_time()
print(f"{day}: {time_slot}")