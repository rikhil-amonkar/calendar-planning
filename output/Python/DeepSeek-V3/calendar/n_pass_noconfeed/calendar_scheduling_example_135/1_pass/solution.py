def find_meeting_time(participants_schedules, meeting_duration, work_hours_start, work_hours_end, day):
    # Convert time strings to minutes since midnight for easier calculation
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    # Convert minutes back to HH:MM format
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"
    
    work_start = time_to_minutes(work_hours_start)
    work_end = time_to_minutes(work_hours_end)
    
    # Collect all busy intervals for all participants
    busy_intervals = []
    for schedule in participants_schedules:
        for busy in schedule:
            start, end = map(time_to_minutes, busy.split(':'))
            busy_intervals.append((start, end))
    
    # Sort intervals by start time
    busy_intervals.sort()
    
    # Find free intervals by merging busy intervals
    free_intervals = []
    prev_end = work_start
    for start, end in busy_intervals:
        if start > prev_end:
            free_intervals.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free_intervals.append((prev_end, work_end))
    
    # Check each free interval for availability across all participants
    # Since the problem states a solution exists, we can return the first suitable interval
    for interval in free_intervals:
        start, end = interval
        if end - start >= meeting_duration:
            meeting_end = start + meeting_duration
            return f"{minutes_to_time(start)}:{minutes_to_time(meeting_end)}"
    
    return None

# Define the problem parameters
participants_schedules = [
    [],  # Eric has no meetings
    ["10:00:10:30", "11:00:12:00", "12:30:13:00", "15:00:16:00"],  # Ashley
    ["9:00:9:30", "10:00:11:30", "12:30:14:00", "14:30:17:00"],  # Ronald
    ["9:00:12:00", "13:00:17:00"],  # Larry
]
meeting_duration = 30  # minutes
work_hours_start = "9:00"
work_hours_end = "17:00"
day = "Monday"

# Find the meeting time
meeting_time = find_meeting_time(participants_schedules, meeting_duration, work_hours_start, work_hours_end, day)

# Output the result
print(f"{meeting_time}:{day}")