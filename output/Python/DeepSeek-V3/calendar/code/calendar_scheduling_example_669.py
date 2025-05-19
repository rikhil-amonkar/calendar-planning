def find_meeting_time():
    # Define work hours and days
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    days = ['Monday', 'Tuesday']
    
    # Define busy slots for Jean and Doris in minutes since midnight
    jean_busy = {
        'Tuesday': [(11 * 60 + 30, 12 * 60), (16 * 60, 16 * 60 + 30)]
    }
    
    doris_busy = {
        'Monday': [(9 * 60, 11 * 60 + 30), (12 * 60, 12 * 60 + 30), 
                   (13 * 60 + 30, 16 * 60), (16 * 60 + 30, 17 * 60)],
        'Tuesday': [(9 * 60, 17 * 60)]
    }
    
    # Doris prefers not to meet on Monday after 14:00
    doris_preference = {
        'Monday': (9 * 60, 14 * 60)
    }
    
    meeting_duration = 30  # minutes
    
    # Iterate through each day to find a suitable time
    for day in days:
        # Get busy slots for the day
        jean_slots = jean_busy.get(day, [])
        doris_slots = doris_busy.get(day, [])
        
        # Combine and sort all busy slots
        all_busy = jean_slots + doris_slots
        all_busy.sort()
        
        # Check Doris's preference for Monday
        if day == 'Monday':
            start, end = doris_preference[day]
        else:
            start, end = work_start, work_end
        
        # Find free slots
        prev_end = start
        free_slots = []
        
        for busy_start, busy_end in all_busy:
            if busy_start > prev_end:
                free_slots.append((prev_end, busy_start))
            prev_end = max(prev_end, busy_end)
        
        if prev_end < end:
            free_slots.append((prev_end, end))
        
        # Check for a slot that can fit the meeting
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
                print(f"{day}, {time_str}")
                return
    
    print("No suitable time found.")

find_meeting_time()