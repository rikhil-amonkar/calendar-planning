def find_meeting_time():
    # Define work hours and days
    work_hours_start = 9 * 60  # 9:00 in minutes
    work_hours_end = 17 * 60   # 17:00 in minutes
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
    
    # Define Juan's busy times in minutes since midnight for each day
    juan_busy = {
        'Monday': [(11 * 60, 11 * 60 + 30)],
        'Tuesday': [(11 * 60 + 30, 12 * 60), (12 * 60 + 30, 13 * 60 + 30), (15 * 60 + 30, 16 * 60)],
        'Wednesday': [(14 * 60 + 30, 15 * 60)],
        'Thursday': [(15 * 60 + 30, 16 * 60)],
        'Friday': [(10 * 60 + 30, 11 * 60)]
    }
    
    # Define Doris's busy times in minutes since midnight for each day
    doris_busy = {
        'Monday': [(9 * 60, 17 * 60)],
        'Tuesday': [(9 * 60, 15 * 60 + 30), (16 * 60, 16 * 60 + 30)],
        'Wednesday': [(9 * 60, 9 * 60 + 30), (10 * 60, 12 * 60 + 30), (14 * 60, 14 * 60 + 30), (15 * 60, 16 * 60), (16 * 60 + 30, 17 * 60)],
        'Thursday': [(9 * 60 + 30, 13 * 60), (14 * 60, 15 * 60 + 30), (16 * 60, 17 * 60)],
        'Friday': [(9 * 60, 10 * 60), (10 * 60 + 30, 12 * 60), (13 * 60, 14 * 60 + 30), (15 * 60, 17 * 60)]
    }
    
    # Doris's preferences to avoid Tuesday and Friday
    preferred_days = ['Monday', 'Wednesday', 'Thursday']
    
    # Iterate through preferred days first, then others
    for day in preferred_days + [d for d in days if d not in preferred_days]:
        # Get busy intervals for both participants
        juan_intervals = juan_busy.get(day, [])
        doris_intervals = doris_busy.get(day, [])
        
        # Merge and sort all busy intervals
        all_busy = juan_intervals + doris_intervals
        all_busy.sort()
        
        # Find free slots
        free_slots = []
        prev_end = work_hours_start
        
        for start, end in all_busy:
            if start > prev_end:
                free_slots.append((prev_end, start))
            prev_end = max(prev_end, end)
        
        if prev_end < work_hours_end:
            free_slots.append((prev_end, work_hours_end))
        
        # Check each free slot for 30-minute availability
        for slot_start, slot_end in free_slots:
            if slot_end - slot_start >= 30:
                # Convert back to HH:MM format
                start_hh = slot_start // 60
                start_mm = slot_start % 60
                end_hh = (slot_start + 30) // 60
                end_mm = (slot_start + 30) % 60
                
                # Format as HH:MM:HH:MM
                return f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}"
    
    return "No suitable time found"

# Output the proposed meeting time
print(find_meeting_time())