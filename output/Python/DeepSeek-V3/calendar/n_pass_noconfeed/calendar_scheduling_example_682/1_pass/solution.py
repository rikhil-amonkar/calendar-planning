def find_meeting_time():
    # Define work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    
    # Define days to consider
    days = ['Monday', 'Tuesday']
    
    # Amanda's busy times in minutes since midnight
    amanda_busy = {
        'Monday': [
            (9 * 60, 10 * 60 + 30),    # 9:00-10:30
            (11 * 60, 11 * 60 + 30),    # 11:00-11:30
            (12 * 60 + 30, 13 * 60),   # 12:30-13:00
            (13 * 60 + 30, 14 * 60),    # 13:30-14:00
            (14 * 60 + 30, 15 * 60),    # 14:30-15:00
        ],
        'Tuesday': [
            (9 * 60, 9 * 60 + 30),     # 9:00-9:30
            (10 * 60, 10 * 60 + 30),    # 10:00-10:30
            (11 * 60 + 30, 12 * 60),   # 11:30-12:00
            (13 * 60 + 30, 14 * 60 + 30), # 13:30-14:30
            (15 * 60 + 30, 16 * 60),    # 15:30-16:00
            (16 * 60 + 30, 17 * 60),    # 16:30-17:00
        ]
    }
    
    # Nathan's busy times in minutes since midnight
    nathan_busy = {
        'Monday': [
            (10 * 60, 10 * 60 + 30),    # 10:00-10:30
            (11 * 60, 11 * 60 + 30),    # 11:00-11:30
            (13 * 60 + 30, 14 * 60 + 30), # 13:30-14:30
            (16 * 60, 16 * 60 + 30),    # 16:00-16:30
        ],
        'Tuesday': [
            (9 * 60, 10 * 60 + 30),    # 9:00-10:30
            (11 * 60, 13 * 60),        # 11:00-13:00
            (13 * 60 + 30, 14 * 60),   # 13:30-14:00
            (14 * 60 + 30, 15 * 60 + 30), # 14:30-15:30
            (16 * 60, 16 * 60 + 30),   # 16:00-16:30
        ]
    }
    
    # Constraints
    amanda_no_tuesday_after_11 = True
    nathan_no_monday = True
    
    meeting_duration = 30  # minutes
    
    # Iterate through days
    for day in days:
        if day == 'Monday' and nathan_no_monday:
            continue
        
        # Combine busy times for Amanda and Nathan
        combined_busy = []
        if day in amanda_busy:
            combined_busy.extend(amanda_busy[day])
        if day in nathan_busy:
            combined_busy.extend(nathan_busy[day])
        
        # Sort busy intervals
        combined_busy.sort()
        
        # Find free slots
        free_slots = []
        prev_end = work_start
        
        for start, end in combined_busy:
            if start > prev_end:
                free_slots.append((prev_end, start))
            prev_end = max(prev_end, end)
        
        if prev_end < work_end:
            free_slots.append((prev_end, work_end))
        
        # Check each free slot for availability
        for slot_start, slot_end in free_slots:
            if slot_end - slot_start >= meeting_duration:
                # Check Amanda's Tuesday after 11 constraint
                if day == 'Tuesday' and amanda_no_tuesday_after_11:
                    if slot_start >= 11 * 60:
                        continue
                    # Adjust slot_end to not exceed 11:00
                    if slot_end > 11 * 60:
                        slot_end = 11 * 60
                        if slot_end - slot_start < meeting_duration:
                            continue
                
                # Found a valid slot
                start_time = f"{slot_start // 60:02d}:{slot_start % 60:02d}"
                end_time = f"{(slot_start + meeting_duration) // 60:02d}:{(slot_start + meeting_duration) % 60:02d}"
                return f"{day}: {start_time}:{end_time}"
    
    return "No suitable time found."

# Execute and print the result
print(find_meeting_time())