def find_meeting_time():
    # Define work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    
    # Define days to check (Monday=0, Tuesday=1)
    days = [0, 1]  # Monday and Tuesday
    
    # Define busy slots for Emily and Sandra in minutes since midnight
    # Format: {day: [(start1, end1), (start2, end2), ...]}
    emily_busy = {
        0: [(12 * 60 + 30, 13 * 60), (13 * 60 + 30, 14 * 60), (16 * 60 + 30, 17 * 60)],
        1: [(9 * 60 + 30, 10 * 60), (11 * 60 + 30, 12 * 60), (12 * 60 + 30, 13 * 60 + 30), (15 * 60 + 30, 16 * 60)]
    }
    
    sandra_busy = {
        0: [(9 * 60, 11 * 60), (11 * 60 + 30, 17 * 60)],
        1: [(9 * 60 + 30, 10 * 60 + 30), (11 * 60, 13 * 60), (13 * 60 + 30, 14 * 60), (15 * 60, 16 * 60)]
    }
    
    meeting_duration = 30  # minutes
    
    # Prefer Monday (day 0) over Tuesday (day 1) due to Emily's preference
    for day in sorted(days):
        # Get all busy slots for both participants on this day
        combined_busy = emily_busy.get(day, []) + sandra_busy.get(day, [])
        combined_busy.sort()
        
        # Find free slots by checking gaps between busy slots and work hours
        prev_end = work_start
        free_slots = []
        
        for start, end in combined_busy:
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
            
            if available_end - available_start >= meeting_duration:
                # Found a suitable slot
                meeting_start = available_start
                meeting_end = meeting_start + meeting_duration
                
                # Convert back to HH:MM format
                def format_time(minutes):
                    hours = minutes // 60
                    mins = minutes % 60
                    return f"{hours:02d}:{mins:02d}"
                
                return f"{format_time(meeting_start)}:{format_time(meeting_end)}"
    
    return "No suitable time found"

# Output the result
print(find_meeting_time())