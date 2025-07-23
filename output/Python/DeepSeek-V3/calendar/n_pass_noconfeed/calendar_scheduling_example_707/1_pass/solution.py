def find_meeting_time():
    # Define work hours and days to consider
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    days = ['Monday', 'Tuesday', 'Wednesday']
    meeting_duration = 30  # minutes
    
    # Define busy times for Ryan and Adam in minutes since midnight
    # Format: {day: [(start1, end1), (start2, end2), ...]}
    ryan_busy = {
        'Monday': [(9*60 + 30, 10*60), (11*60, 12*60), (13*60, 13*60 + 30), (15*60 + 30, 16*60)],
        'Tuesday': [(11*60 + 30, 12*60 + 30), (15*60 + 30, 16*60)],
        'Wednesday': [(12*60, 13*60), (15*60 + 30, 16*60), (16*60 + 30, 17*60)]
    }
    
    adam_busy = {
        'Monday': [(9*60, 10*60 + 30), (11*60, 13*60 + 30), (14*60, 16*60), (16*60 + 30, 17*60)],
        'Tuesday': [(9*60, 10*60), (10*60 + 30, 15*60 + 30), (16*60, 17*60)],
        'Wednesday': [(9*60, 9*60 + 30), (10*60, 11*60), (11*60 + 30, 14*60 + 30), (15*60, 15*60 + 30), (16*60, 16*60 + 30)]
    }
    
    # Apply constraints: Ryan cannot meet on Wednesday, Adam avoids Monday before 14:30
    days_to_check = ['Monday', 'Tuesday']  # Wednesday is excluded for Ryan
    
    for day in days_to_check:
        # Combine and sort busy times for both participants
        combined_busy = ryan_busy.get(day, []) + adam_busy.get(day, [])
        combined_busy.sort()
        
        # Add work hours boundaries
        slots = []
        prev_end = work_start
        
        # If it's Monday and Adam wants to avoid before 14:30, adjust prev_end
        if day == 'Monday':
            prev_end = max(prev_end, 14*60 + 30)
        
        for start, end in combined_busy:
            if start > prev_end:
                slots.append((prev_end, start))
            prev_end = max(prev_end, end)
        
        # Check the slot after last busy time
        if prev_end < work_end:
            slots.append((prev_end, work_end))
        
        # Find the first slot that fits the meeting duration
        for slot_start, slot_end in slots:
            if slot_end - slot_start >= meeting_duration:
                # Convert minutes back to HH:MM format
                start_hh = slot_start // 60
                start_mm = slot_start % 60
                end_hh = (slot_start + meeting_duration) // 60
                end_mm = (slot_start + meeting_duration) % 60
                
                # Format the time as HH:MM:HH:MM
                time_str = f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}"
                return day, time_str
    
    return None, None

day, time = find_meeting_time()
print(f"{day} {time}")