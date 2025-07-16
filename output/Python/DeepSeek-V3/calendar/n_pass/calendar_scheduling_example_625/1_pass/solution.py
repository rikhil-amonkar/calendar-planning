def find_meeting_time():
    # Define work hours and days to consider
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    days = ['Monday', 'Tuesday']
    
    # Harold's blocked times in minutes since midnight for each day
    harold_blocked = {
        'Monday': [(9 * 60, 10 * 60), (10 * 60 + 30, 17 * 60)],
        'Tuesday': [
            (9 * 60, 9 * 60 + 30),
            (10 * 60 + 30, 11 * 60 + 30),
            (12 * 60 + 30, 13 * 60 + 30),
            (14 * 60 + 30, 15 * 60 + 30),
            (16 * 60, 17 * 60)
        ]
    }
    
    # Harold's preferences: avoid Monday and Tuesday before 14:30
    preferred_days = ['Tuesday']
    preferred_time_start = 14 * 60 + 30  # 14:30
    
    meeting_duration = 30  # minutes
    
    # Iterate through preferred days first
    for day in preferred_days:
        # Get Harold's blocked times for the day
        blocked = harold_blocked.get(day, [])
        
        # Check preferred time slot first (Tuesday after 14:30)
        if day == 'Tuesday':
            start = preferred_time_start
            end = start + meeting_duration
            if end > work_end:
                continue  # Doesn't fit in work hours
            
            # Check if the slot is free
            conflict = False
            for block_start, block_end in blocked:
                if not (end <= block_start or start >= block_end):
                    conflict = True
                    break
            
            if not conflict:
                return day, start, end
    
    # If preferred time not available, check other slots (though not needed here)
    for day in days:
        if day in preferred_days:
            continue  # Already checked
        
        blocked = harold_blocked.get(day, [])
        # Generate all possible 30-minute slots in work hours
        for start in range(work_start, work_end - meeting_duration + 1, 15):
            end = start + meeting_duration
            conflict = False
            for block_start, block_end in blocked:
                if not (end <= block_start or start >= block_end):
                    conflict = True
                    break
            if not conflict:
                return day, start, end
    
    return None  # No slot found (though problem states one exists)

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Find the meeting time
day, start, end = find_meeting_time()
start_str = format_time(start)
end_str = format_time(end)

print(f"{day}: {start_str}:{end_str}")