def find_meeting_time():
    # Define work hours and days to consider
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    days = ['Monday', 'Tuesday', 'Wednesday']
    
    # Samuel's busy times in minutes since midnight for each day
    samuel_busy = {
        'Monday': [(10*60 + 30, 11*60), (12*60, 12*60 + 30), (13*60, 15*60), (15*60 + 30, 16*60 + 30)],
        'Tuesday': [(9*60, 12*60), (14*60, 15*60 + 30), (16*60 + 30, 17*60)],
        'Wednesday': [(10*60 + 30, 11*60), (11*60 + 30, 12*60), (12*60 + 30, 13*60), (14*60, 14*60 + 30), (15*60, 16*60)]
    }
    
    # Larry's preferences: avoid Wednesday
    # Samuel's preferences: avoid Tuesday
    preferred_days = ['Monday', 'Tuesday']  # Wednesday is last resort
    
    # Duration in minutes
    duration = 30
    
    # Iterate through days in order of preference
    for day in preferred_days + ['Wednesday']:
        if day == 'Tuesday' and day in preferred_days:
            continue  # Skip Tuesday as Samuel prefers to avoid it
        
        # Get Samuel's busy times for the day
        busy_times = samuel_busy.get(day, [])
        
        # Find all free slots in Samuel's schedule
        free_slots = []
        prev_end = work_start
        
        for start, end in sorted(busy_times):
            if start > prev_end:
                free_slots.append((prev_end, start))
            prev_end = max(prev_end, end)
        
        if work_end > prev_end:
            free_slots.append((prev_end, work_end))
        
        # Check each free slot for availability
        for slot_start, slot_end in free_slots:
            if slot_end - slot_start >= duration:
                # Found a suitable slot
                start_time = slot_start
                end_time = start_time + duration
                
                # Convert times back to HH:MM format
                def format_time(minutes):
                    hours = minutes // 60
                    mins = minutes % 60
                    return f"{hours:02d}:{mins:02d}"
                
                time_range = f"{format_time(start_time)}:{format_time(end_time)}"
                return day, time_range
    
    # Fallback (shouldn't reach here as per problem statement)
    return None, None

day, time_range = find_meeting_time()
print(f"{day}: {time_range}")