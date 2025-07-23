def find_meeting_time(participants_schedules, work_hours, meeting_duration, day):
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"
    
    work_start, work_end = work_hours
    work_start_min = time_to_minutes(work_start)
    work_end_min = time_to_minutes(work_end)
    meeting_duration_min = meeting_duration * 60
    
    busy_intervals = []
    for schedule in participants_schedules:
        for busy in schedule:
            start, end = map(time_to_minutes, busy)
            busy_intervals.append((start, end))
    
    busy_intervals.sort()
    
    merged = []
    for start, end in busy_intervals:
        if not merged:
            merged.append((start, end))
        else:
            last_start, last_end = merged[-1]
            if start <= last_end:
                new_end = max(end, last_end)
                merged[-1] = (last_start, new_end)
            else:
                merged.append((start, end))
    
    print("Merged busy times:")
    for start, end in merged:
        print(f"- {minutes_to_time(start)}-{minutes_to_time(end)}")
    
    available_slots = []
    prev_end = work_start_min
    for start, end in merged:
        if start - prev_end >= meeting_duration_min:
            available_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    
    if work_end_min - prev_end >= meeting_duration_min:
        available_slots.append((prev_end, work_end_min))
    
    if available_slots:
        print(f"\nAvailable meeting times on {day}:")
        return [ (minutes_to_time(s), minutes_to_time(e)) for s, e in available_slots ]
    else:
        print("\nNo suitable time found (no slot long enough where all participants are free).")
        return None

# Define parameters
work_hours = ("9:00", "17:00")
meeting_duration = 30
day = "Monday"

participants_schedules = [
    [("9:00", "10:30"), ("15:30", "16:00")],
    [("11:00", "11:30"), ("12:30", "13:00")],
    [("9:00", "10:30"), ("12:00", "12:30"), ("13:00", "13:30"), ("14:00", "16:30")],
]

# Find meeting times
meeting_times = find_meeting_time(participants_schedules, work_hours, meeting_duration, day)