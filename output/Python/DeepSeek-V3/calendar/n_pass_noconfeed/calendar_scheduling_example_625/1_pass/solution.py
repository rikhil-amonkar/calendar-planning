def find_meeting_time():
    # Define work hours and days to consider
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    days = ['Monday', 'Tuesday']
    
    # Harold's schedule and preferences
    harold_blocked = {
        'Monday': [(9 * 60, 10 * 60), (10.5 * 60, 17 * 60)],
        'Tuesday': [
            (9 * 60, 9.5 * 60),
            (10.5 * 60, 11.5 * 60),
            (12.5 * 60, 13.5 * 60),
            (14.5 * 60, 15.5 * 60),
            (16 * 60, 17 * 60)
        ]
    }
    
    meeting_duration = 30  # minutes
    
    # Check Tuesday first (Harold prefers to avoid Monday)
    for day in ['Tuesday', 'Monday']:
        # Generate all possible 30-minute slots in work hours
        for start in range(work_start, work_end - meeting_duration + 1, 15):
            end = start + meeting_duration
            slot = (start, end)
            
            # Check if the slot is free for Harold
            harold_free = True
            for blocked_start, blocked_end in harold_blocked[day]:
                if not (end <= blocked_start or start >= blocked_end):
                    harold_free = False
                    break
            
            if harold_free:
                # Additional preference checks
                if day == 'Monday' and len(harold_blocked['Monday']) > 1:
                    continue  # Harold wants to avoid more meetings on Monday
                if day == 'Tuesday' and end > 14.5 * 60:
                    continue  # Harold prefers before 14:30 on Tuesday
                
                # Format the time
                start_hour = start // 60
                start_min = start % 60
                end_hour = end // 60
                end_min = end % 60
                
                return (
                    day,
                    f"{start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}"
                )
    
    return None

# Find and print the meeting time
day, time_range = find_meeting_time()
print(f"{day}: {time_range}")