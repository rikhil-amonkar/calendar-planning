def find_meeting_time():
    # Define work hours and days to consider
    work_hours_start = 9 * 60  # 9:00 in minutes
    work_hours_end = 17 * 60    # 17:00 in minutes
    days = ['Monday', 'Tuesday', 'Wednesday']
    
    # Define blocked times for each participant in minutes since midnight
    susan_blocked = {
        'Monday': [(12 * 60 + 30, 13 * 60), (13 * 60 + 30, 14 * 60)],
        'Tuesday': [(11 * 60 + 30, 12 * 60)],
        'Wednesday': [(9 * 60 + 30, 10 * 60 + 30), (14 * 60, 14 * 60 + 30), (15 * 60 + 30, 16 * 60 + 30)]
    }
    
    sandra_blocked = {
        'Monday': [(9 * 60, 13 * 60), (14 * 60, 15 * 60), (16 * 60, 16 * 60 + 30)],
        'Tuesday': [(9 * 60, 9 * 60 + 30), (10 * 60 + 30, 12 * 60), (12 * 60 + 30, 13 * 60 + 30), (14 * 60, 14 * 60 + 30), (16 * 60, 17 * 60)],
        'Wednesday': [(9 * 60, 11 * 60 + 30), (12 * 60, 12 * 60 + 30), (13 * 60, 17 * 60)]
    }
    
    meeting_duration = 30  # minutes
    
    # Iterate through each day
    for day in days:
        # Skip Tuesday if Susan prefers not to meet then
        if day == 'Tuesday':
            continue
        
        # Get blocked times for both participants
        susan_day = susan_blocked.get(day, [])
        sandra_day = sandra_blocked.get(day, [])
        
        # Combine and sort all blocked times
        all_blocked = susan_day + sandra_day
        all_blocked.sort()
        
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
        
        # Check for a slot that fits the meeting duration
        for slot_start, slot_end in available_slots:
            if slot_end - slot_start >= meeting_duration:
                # Found a suitable slot
                meeting_start = slot_start
                meeting_end = meeting_start + meeting_duration
                
                # Convert back to HH:MM format
                def minutes_to_time(minutes):
                    hours = minutes // 60
                    mins = minutes % 60
                    return f"{hours:02d}:{mins:02d}"
                
                time_str = f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
                print(f"{day}: {time_str}")
                return
    
    print("No suitable time found.")

find_meeting_time()