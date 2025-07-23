def find_meeting_time():
    # Define work hours and days to consider
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    days = ['Monday', 'Tuesday', 'Wednesday']
    
    # Roy's busy times in minutes since midnight for each day
    roy_busy = {
        'Monday': [
            (10 * 60, 11 * 60 + 30),
            (12 * 60, 13 * 60),
            (14 * 60, 14 * 60 + 30),
            (15 * 60, 17 * 60)
        ],
        'Tuesday': [
            (10 * 60 + 30, 11 * 60 + 30),
            (12 * 60, 14 * 60 + 30),
            (15 * 60, 15 * 60 + 30),
            (16 * 60, 17 * 60)
        ],
        'Wednesday': [
            (9 * 60 + 30, 11 * 60 + 30),
            (12 * 60 + 30, 14 * 60),
            (14 * 60 + 30, 15 * 60 + 30),
            (16 * 60 + 30, 17 * 60)
        ]
    }
    
    # Patrick is free all the time, so only Roy's schedule matters
    meeting_duration = 60  # 1 hour in minutes
    
    for day in days:
        # Get Roy's busy times for the day
        busy_times = roy_busy[day]
        # Sort busy times by start time
        busy_times.sort()
        
        # Check before first busy block
        first_busy_start = busy_times[0][0]
        if first_busy_start - work_start >= meeting_duration:
            start_time = work_start
            end_time = start_time + meeting_duration
            return day, start_time, end_time
        
        # Check between busy blocks
        for i in range(len(busy_times) - 1):
            current_end = busy_times[i][1]
            next_start = busy_times[i + 1][0]
            if next_start - current_end >= meeting_duration:
                start_time = current_end
                end_time = start_time + meeting_duration
                return day, start_time, end_time
        
        # Check after last busy block
        last_busy_end = busy_times[-1][1]
        if work_end - last_busy_end >= meeting_duration:
            start_time = last_busy_end
            end_time = start_time + meeting_duration
            return day, start_time, end_time
    
    return None  # Should not reach here as per problem statement

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

day, start_time, end_time = find_meeting_time()
start_str = format_time(start_time)
end_str = format_time(end_time)
print(f"{day}:{start_str}:{end_str}")