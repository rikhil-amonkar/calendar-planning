def find_meeting_time(participants_schedules, preferences, duration, work_hours_start, work_hours_end, day):
    # Convert time strings to minutes since midnight for easier calculations
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    work_start = time_to_minutes(work_hours_start)
    work_end = time_to_minutes(work_hours_end)
    duration_min = duration * 60

    # Collect all busy intervals for all participants
    busy_intervals = []
    for schedule in participants_schedules.values():
        for interval in schedule:
            start, end = map(time_to_minutes, interval.split(' to '))
            busy_intervals.append((start, end))
    
    # Add preference constraints as busy intervals
    for constraint in preferences.get('avoid_after', []):
        avoid_after_time = time_to_minutes(constraint['time'])
        busy_intervals.append((avoid_after_time, work_end))
    
    # Sort all busy intervals by start time
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

    # Find the first free interval that can accommodate the meeting
    for start, end in free_intervals:
        if end - start >= duration_min:
            meeting_start = start
            meeting_end = meeting_start + duration_min
            return (minutes_to_time(meeting_start), minutes_to_time(meeting_end))
    
    return None, None

# Define the problem
participants_schedules = {
    "Eric": ["12:00 to 13:00", "14:00 to 15:00"],
    "Henry": ["9:30 to 10:00", "10:30 to 11:00", "11:30 to 12:30", "13:00 to 13:30", "14:30 to 15:00", "16:00 to 17:00"]
}

preferences = {
    "Henry": {"avoid_after": [{"time": "10:00"}]}
}

duration = 0.5  # half an hour
work_hours_start = "9:00"
work_hours_end = "17:00"
day = "Monday"

# Find the meeting time
start_time, end_time = find_meeting_time(participants_schedules, preferences, duration, work_hours_start, work_hours_end, day)

# Output the result
if start_time and end_time:
    print(f"{day}: {start_time} to {end_time}")
else:
    print("No suitable time found.")