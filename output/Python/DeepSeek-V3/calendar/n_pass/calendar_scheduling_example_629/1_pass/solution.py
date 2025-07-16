def find_meeting_time():
    # Define work hours and days to consider
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    days = ['Monday', 'Tuesday']
    
    # Define participants' blocked times in minutes since midnight
    # Format: {day: [(start1, end1), (start2, end2), ...]}
    margaret_blocked = {
        'Monday': [
            (10 * 60 + 30, 11 * 60),
            (11 * 60 + 30, 12 * 60),
            (13 * 60, 13 * 60 + 30),
            (15 * 60, 17 * 60)
        ],
        'Tuesday': [
            (12 * 60, 12 * 60 + 30)
        ]
    }
    
    alexis_blocked = {
        'Monday': [
            (9 * 60 + 30, 11 * 60 + 30),
            (12 * 60 + 30, 13 * 60),
            (14 * 60, 17 * 60)
        ],
        'Tuesday': [
            (9 * 60, 9 * 60 + 30),
            (10 * 60, 10 * 60 + 30),
            (14 * 60, 16 * 60 + 30)
        ]
    }
    
    # Margaret's constraints: not Monday, and not Tuesday before 14:30
    preferred_days = ['Tuesday']
    margaret_min_time = 14 * 60 + 30  # 14:30
    
    meeting_duration = 30  # minutes
    
    # Iterate through preferred days (only Tuesday in this case)
    for day in preferred_days:
        # Combine all blocked times for both participants on this day
        all_blocked = margaret_blocked.get(day, []) + alexis_blocked.get(day, [])
        all_blocked.sort()  # Sort by start time
        
        # Find available slots
        available_slots = []
        prev_end = work_start
        
        # Adjust start time based on Margaret's preference
        if day == 'Tuesday':
            prev_end = max(prev_end, margaret_min_time)
        
        for block_start, block_end in all_blocked:
            if block_start > prev_end:
                available_slots.append((prev_end, block_start))
            prev_end = max(prev_end, block_end)
        
        # Check after last block
        if prev_end < work_end:
            available_slots.append((prev_end, work_end))
        
        # Find first slot that fits the meeting duration
        for slot_start, slot_end in available_slots:
            if slot_end - slot_start >= meeting_duration:
                meeting_start = slot_start
                meeting_end = meeting_start + meeting_duration
                # Convert minutes back to HH:MM format
                def format_time(minutes):
                    hours = minutes // 60
                    mins = minutes % 60
                    return f"{hours:02d}:{mins:02d}"
                time_str = f"{format_time(meeting_start)}:{format_time(meeting_end)}"
                return day, time_str
    
    return None, None

day, time_range = find_meeting_time()
print(f"{day}: {time_range}")