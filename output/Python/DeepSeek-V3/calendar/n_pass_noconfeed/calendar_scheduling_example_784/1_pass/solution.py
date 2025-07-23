def find_meeting_time():
    # Define work hours and days to consider
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    days = ['Monday', 'Tuesday', 'Wednesday']
    meeting_duration = 60  # 1 hour in minutes

    # Define blocked times for each participant per day in minutes since midnight
    # Judith's blocked times
    judith_blocked = {
        'Monday': [(12 * 60, 12 * 60 + 30)],
        'Wednesday': [(11 * 60 + 30, 12 * 60)],
    }

    # Timothy's blocked times
    timothy_blocked = {
        'Monday': [
            (9 * 60 + 30, 10 * 60),
            (10 * 60 + 30, 11 * 60 + 30),
            (12 * 60 + 30, 14 * 60),
            (15 * 60 + 30, 17 * 60),
        ],
        'Tuesday': [
            (9 * 60 + 30, 13 * 60),
            (13 * 60 + 30, 14 * 60),
            (14 * 60 + 30, 17 * 60),
        ],
        'Wednesday': [
            (9 * 60, 9 * 60 + 30),
            (10 * 60 + 30, 11 * 60),
            (13 * 60 + 30, 14 * 60 + 30),
            (15 * 60, 15 * 60 + 30),
            (16 * 60, 16 * 60 + 30),
        ],
    }

    # Judith's preferences: avoid Monday and Wednesday before 12:00
    preferred_days = ['Tuesday', 'Wednesday']
    avoid_wed_before_12 = True

    # Iterate through each day to find a suitable time
    for day in preferred_days:
        # Get all blocked times for both participants on this day
        blocked_times = []
        if day in judith_blocked:
            blocked_times.extend(judith_blocked[day])
        if day in timothy_blocked:
            blocked_times.extend(timothy_blocked[day])
        
        # Sort blocked times by start time
        blocked_times.sort()

        # Generate available slots by finding gaps between blocked times
        available_slots = []
        prev_end = work_start

        for start, end in blocked_times:
            if start > prev_end:
                available_slots.append((prev_end, start))
            prev_end = max(prev_end, end)
        
        # Check the slot after the last blocked time
        if prev_end < work_end:
            available_slots.append((prev_end, work_end))

        # Check each available slot for a meeting duration
        for slot_start, slot_end in available_slots:
            if slot_end - slot_start >= meeting_duration:
                # Check Judith's preference for Wednesday before 12:00
                if day == 'Wednesday' and avoid_wed_before_12:
                    if slot_start < 12 * 60:
                        continue  # Skip this slot
                
                # Found a suitable time
                meeting_start = slot_start
                meeting_end = meeting_start + meeting_duration
                
                # Format the time as HH:MM:HH:MM
                start_hh = meeting_start // 60
                start_mm = meeting_start % 60
                end_hh = meeting_end // 60
                end_mm = meeting_end % 60
                
                time_str = f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}"
                return day, time_str

    # If no time found in preferred days, check Monday (though Judith prefers to avoid)
    day = 'Monday'
    blocked_times = []
    if day in judith_blocked:
        blocked_times.extend(judith_blocked[day])
    if day in timothy_blocked:
        blocked_times.extend(timothy_blocked[day])
    
    blocked_times.sort()
    available_slots = []
    prev_end = work_start

    for start, end in blocked_times:
        if start > prev_end:
            available_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    
    if prev_end < work_end:
        available_slots.append((prev_end, work_end))

    for slot_start, slot_end in available_slots:
        if slot_end - slot_start >= meeting_duration:
            meeting_start = slot_start
            meeting_end = meeting_start + meeting_duration
            
            start_hh = meeting_start // 60
            start_mm = meeting_start % 60
            end_hh = meeting_end // 60
            end_mm = meeting_end % 60
            
            time_str = f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}"
            return day, time_str

    return "No suitable time found", "00:00:00:00"

# Run the function and print the result
day, time_range = find_meeting_time()
print(f"{day}: {time_range}")