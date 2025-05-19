def find_meeting_time():
    # Define work hours and days
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    days = ['Monday', 'Tuesday']
    
    # Define busy slots for each person in minutes since midnight
    # Format: (day_index, start_min, end_min)
    russell_busy = [
        (0, 10 * 60 + 30, 11 * 60),  # Monday 10:30-11:00
        (1, 13 * 60, 13 * 60 + 30)    # Tuesday 13:00-13:30
    ]
    
    alexander_busy = [
        (0, 9 * 60, 11 * 60 + 30),    # Monday 9:00-11:30
        (0, 12 * 60, 14 * 60 + 30),   # Monday 12:00-14:30
        (0, 15 * 60, 17 * 60),        # Monday 15:00-17:00
        (1, 9 * 60, 10 * 60),         # Tuesday 9:00-10:00
        (1, 13 * 60, 14 * 60),        # Tuesday 13:00-14:00
        (1, 15 * 60, 15 * 60 + 30),  # Tuesday 15:00-15:30
        (1, 16 * 60, 16 * 60 + 30)    # Tuesday 16:00-16:30
    ]
    
    meeting_duration = 60  # 1 hour in minutes
    
    # Check each day for available slots
    for day_idx in range(2):
        day = days[day_idx]
        
        # Collect all busy slots for both people on this day
        busy_slots = []
        
        # Add Russell's busy slots for the day
        for slot in russell_busy:
            if slot[0] == day_idx:
                busy_slots.append((slot[1], slot[2]))
        
        # Add Alexander's busy slots for the day
        for slot in alexander_busy:
            if slot[0] == day_idx:
                busy_slots.append((slot[1], slot[2]))
        
        # Sort busy slots by start time
        busy_slots.sort()
        
        # Find free slots between work hours
        prev_end = work_start
        free_slots = []
        
        for start, end in busy_slots:
            if start > prev_end:
                free_slots.append((prev_end, start))
            prev_end = max(prev_end, end)
        
        # Check after last busy slot
        if prev_end < work_end:
            free_slots.append((prev_end, work_end))
        
        # Check each free slot for availability
        for slot_start, slot_end in free_slots:
            available_start = slot_start
            available_end = slot_end
            
            # Ensure the slot is at least meeting_duration long
            if available_end - available_start >= meeting_duration:
                # Apply Russell's preference: not Tuesday before 13:30
                if day == 'Tuesday' and available_start < 13 * 60 + 30:
                    continue
                
                # Found a suitable slot
                start_hour = available_start // 60
                start_min = available_start % 60
                end_hour = (available_start + meeting_duration) // 60
                end_min = (available_start + meeting_duration) % 60
                
                # Format the time as HH:MM:HH:MM
                time_str = f"{start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}"
                return day, time_str
    
    return None, None

day, time = find_meeting_time()
print(f"{day}: {time}")