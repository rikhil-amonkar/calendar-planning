def find_meeting_time():
    # Define work hours and days to consider
    work_hours_start = 9 * 60  # 9:00 in minutes
    work_hours_end = 17 * 60    # 17:00 in minutes
    days = ['Monday', 'Tuesday', 'Wednesday']
    
    # Define blocked times for each participant per day in minutes since midnight
    blocked_times = {
        'Judith': {
            'Monday': [(12 * 60, 12 * 60 + 30)],  # 12:00-12:30
            'Wednesday': [(11 * 60 + 30, 12 * 60)], # 11:30-12:00
        },
        'Timothy': {
            'Monday': [
                (9 * 60 + 30, 10 * 60),         # 9:30-10:00
                (10 * 60 + 30, 11 * 60 + 30),    # 10:30-11:30
                (12 * 60 + 30, 14 * 60),         # 12:30-14:00
                (15 * 60 + 30, 17 * 60),         # 15:30-17:00
            ],
            'Tuesday': [
                (9 * 60 + 30, 13 * 60),          # 9:30-13:00
                (13 * 60 + 30, 14 * 60),         # 13:30-14:00
                (14 * 60 + 30, 17 * 60),         # 14:30-17:00
            ],
            'Wednesday': [
                (9 * 60, 9 * 60 + 30),           # 9:00-9:30
                (10 * 60 + 30, 11 * 60),         # 10:30-11:00
                (13 * 60 + 30, 14 * 60 + 30),     # 13:30-14:30
                (15 * 60, 15 * 60 + 30),          # 15:00-15:30
                (16 * 60, 16 * 60 + 30),         # 16:00-16:30
            ],
        },
    }
    
    # Preferences: Judith wants to avoid Monday and Wednesday before 12:00
    preferred_days = ['Tuesday', 'Wednesday']
    
    # Meeting duration in minutes
    meeting_duration = 60
    
    # Iterate through days in preferred order
    for day in preferred_days:
        if day == 'Monday':
            continue  # Judith prefers to avoid Monday
        
        # Get all blocked times for both participants on this day
        judith_blocked = blocked_times['Judith'].get(day, [])
        timothy_blocked = blocked_times['Timothy'].get(day, [])
        all_blocked = judith_blocked + timothy_blocked
        all_blocked.sort()  # Sort by start time
        
        # Find available slots
        available_slots = []
        prev_end = work_hours_start
        
        for start, end in all_blocked:
            if start > prev_end:
                available_slots.append((prev_end, start))
            prev_end = max(prev_end, end)
        
        # Check after last blocked time
        if prev_end < work_hours_end:
            available_slots.append((prev_end, work_hours_end))
        
        # Check each available slot for meeting duration
        for slot_start, slot_end in available_slots:
            if day == 'Wednesday' and slot_start < 12 * 60:
                continue  # Judith prefers to avoid Wednesday before 12:00
            
            if slot_end - slot_start >= meeting_duration:
                meeting_start = slot_start
                meeting_end = meeting_start + meeting_duration
                # Format the time as HH:MM:HH:MM
                start_str = f"{meeting_start // 60:02d}:{meeting_start % 60:02d}"
                end_str = f"{meeting_end // 60:02d}:{meeting_end % 60:02d}"
                return f"{day}: {start_str}:{end_str}"
    
    # If no preferred day works, check Monday (though Judith prefers to avoid)
    day = 'Monday'
    judith_blocked = blocked_times['Judith'].get(day, [])
    timothy_blocked = blocked_times['Timothy'].get(day, [])
    all_blocked = judith_blocked + timothy_blocked
    all_blocked.sort()
    
    prev_end = work_hours_start
    for start, end in all_blocked:
        if start > prev_end:
            available_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    
    if prev_end < work_hours_end:
        available_slots.append((prev_end, work_hours_end))
    
    for slot_start, slot_end in available_slots:
        if slot_end - slot_start >= meeting_duration:
            meeting_start = slot_start
            meeting_end = meeting_start + meeting_duration
            start_str = f"{meeting_start // 60:02d}:{meeting_start % 60:02d}"
            end_str = f"{meeting_end // 60:02d}:{meeting_end % 60:02d}"
            return f"{day}: {start_str}:{end_str}"
    
    return "No suitable time found."

# Run the function and print the result
print(find_meeting_time())