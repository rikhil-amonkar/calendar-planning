def find_meeting_time(participants_schedules, meeting_duration, work_hours_start, work_hours_end, day):
    # Convert time strings to minutes since 9:00 (work_hours_start)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return (hh - work_hours_start) * 60 + mm
    
    def minutes_to_time(minutes):
        hh = work_hours_start + (minutes // 60)
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"
    
    work_start_min = time_to_minutes(f"{work_hours_start}:00")
    work_end_min = time_to_minutes(f"{work_hours_end}:00")
    
    # Collect all busy intervals for all participants
    busy_intervals = []
    for schedule in participants_schedules:
        for busy in schedule:
            # Split the combined time string into start and end times
            parts = busy.split(':')
            start_time = ':'.join(parts[:2])
            end_time = ':'.join(parts[2:])
            start = time_to_minutes(start_time)
            end = time_to_minutes(end_time)
            busy_intervals.append((start, end))
    
    # Sort busy intervals by start time
    busy_intervals.sort()
    
    # Find free intervals by merging busy intervals
    free_intervals = []
    prev_end = work_start_min
    
    for start, end in busy_intervals:
        if start > prev_end:
            free_intervals.append((prev_end, start))
        prev_end = max(prev_end, end)
    
    if prev_end < work_end_min:
        free_intervals.append((prev_end, work_end_min))
    
    # Find the earliest free interval that can fit the meeting
    for start, end in free_intervals:
        if end - start >= meeting_duration:
            meeting_start = start
            meeting_end = meeting_start + meeting_duration
            return (
                f"{minutes_to_time(meeting_start)}-{minutes_to_time(meeting_end)}",
                day
            )
    
    return None

# Define participants' schedules (busy times in HH:MM:HH:MM format)
participants_schedules = [
    [],  # Steven is free
    [],  # Roy is free
    ["09:30:10:30", "11:30:12:00", "13:00:13:30", "15:00:16:00"],  # Cynthia
    ["09:00:09:30", "10:30:11:00", "11:30:12:00", "13:00:13:30", "14:00:14:30", "15:00:15:30", "16:00:17:00"],  # Lauren
    ["10:30:11:00", "11:30:12:00", "12:30:13:30", "14:00:16:00"],  # Robert
]

meeting_duration = 30  # minutes
work_hours_start = 9
work_hours_end = 17
day = "Monday"

result = find_meeting_time(
    participants_schedules,
    meeting_duration,
    work_hours_start,
    work_hours_end,
    day
)

if result:
    meeting_time, day_of_week = result
    print(f"{meeting_time} on {day_of_week}")
else:
    print("No available meeting time found")