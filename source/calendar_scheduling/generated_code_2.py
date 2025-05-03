def find_meeting_time():
    # Define work hours and days
    work_hours_start = 9 * 60  # 9:00 in minutes
    work_hours_end = 17 * 60   # 17:00 in minutes
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
    
    # Define Jordan's busy times in minutes since midnight
    jordan_busy = {
        'Monday': [(9 * 60 + 30, 10 * 60)],
        'Thursday': [(12 * 60, 12 * 60 + 30)]
    }
    
    # Define Michael's busy times in minutes since midnight
    michael_busy = {
        'Monday': [
            (10 * 60, 11 * 60),
            (11 * 60 + 30, 13 * 60),
            (13 * 60 + 30, 16 * 60),
            (16 * 60 + 30, 17 * 60)
        ],
        'Tuesday': [
            (9 * 60 + 30, 10 * 60),
            (10 * 60 + 30, 11 * 60),
            (11 * 60 + 30, 12 * 60),
            (12 * 60 + 30, 13 * 60),
            (13 * 60 + 30, 14 * 60),
            (15 * 60, 16 * 60),
            (16 * 60 + 30, 17 * 60)
        ],
        'Wednesday': [
            (9 * 60, 9 * 60 + 30),
            (10 * 60, 16 * 60 + 30)
        ],
        'Thursday': [
            (10 * 60, 10 * 60 + 30),
            (11 * 60, 14 * 60 + 30),
            (15 * 60, 15 * 60 + 30),
            (16 * 60 + 30, 17 * 60)
        ],
        'Friday': [
            (10 * 60 + 30, 11 * 60 + 30),
            (12 * 60, 13 * 60 + 30),
            (14 * 60, 15 * 60),
            (15 * 60 + 30, 16 * 60 + 30)
        ]
    }
    
    # Iterate through each day to find the earliest available slot
    for day in days:
        # Collect all busy intervals for both participants
        busy_intervals = []
        
        # Add Jordan's busy times for the day
        if day in jordan_busy:
            busy_intervals.extend(jordan_busy[day])
        
        # Add Michael's busy times for the day
        if day in michael_busy:
            busy_intervals.extend(michael_busy[day])
        
        # Sort all busy intervals by start time
        busy_intervals.sort()
        
        # Check the time before the first busy interval
        prev_end = work_hours_start
        for interval in busy_intervals:
            start, end = interval
            if start > prev_end and (start - prev_end) >= 60:
                # Found a suitable slot
                meeting_start = prev_end
                meeting_end = meeting_start + 60
                return f"{meeting_start // 60:02d}:{meeting_start % 60:02d}:{meeting_end // 60:02d}:{meeting_end % 60:02d}"
            prev_end = max(prev_end, end)
        
        # Check the time after the last busy interval
        if work_hours_end - prev_end >= 60:
            meeting_start = prev_end
            meeting_end = meeting_start + 60
            return f"{meeting_start // 60:02d}:{meeting_start % 60:02d}:{meeting_end // 60:02d}:{meeting_end % 60:02d}"
    
    return "No suitable time found"

print(find_meeting_time())