def find_meeting_time(participants_schedules, work_hours, duration_minutes, day):
    # Convert time strings to minutes since 9:00 (start of work hours)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return (hh - 9) * 60 + mm  # Assuming work_hours start at 9:00

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = 9 + (minutes // 60)
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    start_work = time_to_minutes(work_hours[0])
    end_work = time_to_minutes(work_hours[1])
    duration = duration_minutes

    # Collect all busy intervals for all participants
    busy_intervals = []
    for schedule in participants_schedules:
        for busy in schedule:
            start, end = map(time_to_minutes, busy)
            busy_intervals.append((start, end))
    
    # Sort intervals by start time
    busy_intervals.sort()

    # Merge overlapping or adjacent intervals
    merged = []
    for start, end in busy_intervals:
        if not merged:
            merged.append([start, end])
        else:
            last_start, last_end = merged[-1]
            if start <= last_end:
                merged[-1][1] = max(end, last_end)
            else:
                merged.append([start, end])

    # Find the first available slot
    prev_end = start_work
    for start, end in merged:
        if start - prev_end >= duration:
            available_start = prev_end
            available_end = available_start + duration
            return (minutes_to_time(available_start), minutes_to_time(available_end))
        prev_end = max(prev_end, end)
    
    # Check after last busy interval
    if end_work - prev_end >= duration:
        available_start = prev_end
        available_end = available_start + duration
        return (minutes_to_time(available_start), minutes_to_time(available_end))
    
    return None

# Define work hours and day
work_hours = ("9:00", "17:00")
day = "Monday"
duration_minutes = 30

# Define each participant's busy times
participants_schedules = [
    [],  # Eric has no meetings
    [("10:00", "10:30"), ("11:00", "12:00"), ("12:30", "13:00"), ("15:00", "16:00")],  # Ashley
    [("9:00", "9:30"), ("10:00", "11:30"), ("12:30", "14:00"), ("14:30", "17:00")],  # Ronald
    [("9:00", "12:00"), ("13:00", "17:00")],  # Larry
]

# Find the meeting time
meeting_time = find_meeting_time(participants_schedules, work_hours, duration_minutes, day)

# Output the result
if meeting_time:
    start, end = meeting_time
    print(f"{start}:{end}:{day}")
else:
    print("No available time slot found.")