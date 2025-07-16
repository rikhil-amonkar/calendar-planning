def find_meeting_time(participants_schedules, meeting_duration, work_hours_start, work_hours_end):
    # Convert time strings to minutes since midnight for easier calculation
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"
    
    work_start = time_to_minutes(work_hours_start)
    work_end = time_to_minutes(work_hours_end)
    duration = meeting_duration
    
    # Collect all busy intervals for all participants
    busy_intervals = []
    for schedule in participants_schedules:
        for interval in schedule:
            # Split the interval into start and end times
            start_time, end_time = interval.split(':')[:2], interval.split(':')[2:]
            start = time_to_minutes(f"{start_time[0]}:{start_time[1]}")
            end = time_to_minutes(f"{end_time[0]}:{end_time[1]}")
            busy_intervals.append((start, end))
    
    # Sort all busy intervals by start time
    busy_intervals.sort()
    
    # Find all free intervals by merging busy intervals
    free_intervals = []
    prev_end = work_start
    
    for start, end in busy_intervals:
        if start > prev_end:
            free_intervals.append((prev_end, start))
        prev_end = max(prev_end, end)
    
    if prev_end < work_end:
        free_intervals.append((prev_end, work_end))
    
    # Find the first free interval that can accommodate the meeting
    for interval in free_intervals:
        start, end = interval
        if end - start >= duration:
            meeting_start = start
            meeting_end = meeting_start + duration
            return (minutes_to_time(meeting_start), minutes_to_time(meeting_end))
    
    return None

# Define participants' schedules
participants_schedules = [
    ["13:00:13:30", "16:00:16:30"],  # Judy
    ["10:00:10:30", "12:00:13:00", "14:00:14:30"],  # Olivia
    [],  # Eric
    ["10:00:10:30", "15:00:15:30"],  # Jacqueline
    ["09:00:10:00", "10:30:12:00", "13:00:13:30", "14:30:15:00", "15:30:17:00"],  # Laura
    ["09:00:10:00", "11:00:11:30", "12:30:13:00", "14:00:14:30", "15:30:17:00"],  # Tyler
    ["09:30:10:30", "11:00:11:30", "12:00:12:30", "13:00:13:30", "14:00:14:30", "16:00:17:00"],  # Lisa
]

# Meeting duration in minutes (30 minutes)
meeting_duration = 30
work_hours_start = "09:00"
work_hours_end = "17:00"

# Find the meeting time
meeting_time = find_meeting_time(participants_schedules, meeting_duration, work_hours_start, work_hours_end)

if meeting_time:
    start_time, end_time = meeting_time
    print(f"{{{start_time}:{end_time}}}")
    print("Monday")
else:
    print("No suitable time found.")