def find_meeting_time():
    # Define work hours and days
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    days = ['Monday', 'Tuesday']
    
    # Harold's blocked times in minutes since midnight for each day
    harold_blocked = {
        'Monday': [
            (9 * 60, 10 * 60),      # 9:00-10:00
            (10 * 60 + 30, 17 * 60) # 10:30-17:00
        ],
        'Tuesday': [
            (9 * 60, 9 * 60 + 30),      # 9:00-9:30
            (10 * 60 + 30, 11 * 60 + 30), # 10:30-11:30
            (12 * 60 + 30, 13 * 60 + 30), # 12:30-13:30
            (14 * 60 + 30, 15 * 60 + 30), # 14:30-15:30
            (16 * 60, 17 * 60)            # 16:00-17:00
        ]
    }
    
    # Harold's preferences: avoid Monday and Tuesday before 14:30
    preferred_day = 'Tuesday'
    preferred_time = 14 * 60 + 30  # 14:30
    
    meeting_duration = 30  # minutes
    
    # Check preferred day and time first (Tuesday after 14:30)
    if preferred_day == 'Tuesday':
        # Find gaps on Tuesday after 14:30
        blocked_times = harold_blocked['Tuesday']
        # Add work hours as boundaries
        blocked_times_sorted = sorted(blocked_times + [(work_start, work_start), (work_end, work_end)])
        
        # Iterate through blocked times to find a gap
        for i in range(len(blocked_times_sorted) - 1):
            current_end = blocked_times_sorted[i][1]
            next_start = blocked_times_sorted[i + 1][0]
            if current_end >= preferred_time and next_start - current_end >= meeting_duration:
                start_time = current_end
                end_time = start_time + meeting_duration
                return 'Tuesday', f"{format_time(start_time)}:{format_time(end_time)}"
    
    # If preferred time not available, check other times
    for day in days:
        if day == 'Monday' and preferred_day == 'Tuesday':
            continue  # skip Monday if Harold prefers Tuesday
        
        blocked_times = harold_blocked[day]
        blocked_times_sorted = sorted(blocked_times + [(work_start, work_start), (work_end, work_end)])
        
        for i in range(len(blocked_times_sorted) - 1):
            current_end = blocked_times_sorted[i][1]
            next_start = blocked_times_sorted[i + 1][0]
            if next_start - current_end >= meeting_duration:
                start_time = current_end
                end_time = start_time + meeting_duration
                # Check Harold's preference for Tuesday before 14:30
                if day == 'Tuesday' and end_time <= preferred_time:
                    continue  # skip if before 14:30 on Tuesday
                return day, f"{format_time(start_time)}:{format_time(end_time)}"
    
    return None, "00:00:00:00"  # fallback (shouldn't reach here per problem statement)

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

day, time_range = find_meeting_time()
print(f"{day}, {time_range}")