def find_meeting_time(participants_schedules, work_hours, meeting_duration, day):
    # Convert time strings to minutes for easier calculation
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"
    
    work_start, work_end = work_hours
    work_start_min = time_to_minutes(work_start)
    work_end_min = time_to_minutes(work_end)
    meeting_duration_min = meeting_duration * 60
    
    # Collect all busy intervals for all participants
    busy_intervals = []
    for schedule in participants_schedules:
        for busy in schedule:
            start, end = map(time_to_minutes, busy)
            busy_intervals.append((start, end))
    
    # Sort all busy intervals by start time
    busy_intervals.sort()
    
    # Merge overlapping or adjacent busy intervals
    merged = []
    for start, end in busy_intervals:
        if not merged:
            merged.append((start, end))
        else:
            last_start, last_end = merged[-1]
            if start <= last_end:
                # Overlapping or adjacent, merge them
                new_end = max(end, last_end)
                merged[-1] = (last_start, new_end)
            else:
                merged.append((start, end))
    
    # Find the first available slot that fits the meeting duration
    prev_end = work_start_min
    for start, end in merged:
        # Check if there's enough time before the current busy interval
        if start - prev_end >= meeting_duration_min:
            available_start = prev_end
            available_end = available_start + meeting_duration_min
            return (minutes_to_time(available_start), minutes_to_time(available_end))
        prev_end = max(prev_end, end)
    
    # Check after the last busy interval
    if work_end_min - prev_end >= meeting_duration_min:
        available_start = prev_end
        available_end = available_start + meeting_duration_min
        return (minutes_to_time(available_start), minutes_to_time(available_end))
    
    return None

# Define work hours, meeting duration, and day
work_hours = ("9:00", "17:00")
meeting_duration = 30  # minutes
day = "Monday"

# Define participants' schedules in HH:MM format
participants_schedules = [
    [("9:00", "10:30"), ("15:30", "16:00")],  # Juan
    [("11:00", "11:30"), ("12:30", "13:00")],  # Marilyn
    [("9:00", "10:30"), ("12:00", "12:30"), ("13:00", "13:30"), ("14:00", "16:30")],  # Ronald
]

# Find the meeting time
meeting_time = find_meeting_time(participants_schedules, work_hours, meeting_duration, day)

# Output the result
if meeting_time:
    start, end = meeting_time
    print(f"{day}: {start}-{end}")
else:
    print("No suitable time found.")