def find_meeting_time(participants_schedules, work_hours, meeting_duration, days):
    # Convert time strings to minutes since 9:00 (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm - 540  # Subtract 540 to start from 0 (9:00)
    
    def minutes_to_time(minutes):
        total_minutes = minutes + 540
        hh = total_minutes // 60
        mm = total_minutes % 60
        return f"{hh:02d}:{mm:02d}"
    
    work_start, work_end = work_hours.split(' to ')
    work_start_min = time_to_minutes(work_start)
    work_end_min = time_to_minutes(work_end)
    
    meeting_duration_min = meeting_duration * 60
    
    for day in days:
        # Collect all busy intervals for the day
        busy_intervals = []
        for participant in participants_schedules:
            for entry in participant.get(day, []):
                start, end = entry.split(' to ')
                start_min = time_to_minutes(start)
                end_min = time_to_minutes(end)
                busy_intervals.append((start_min, end_min))
        
        # Sort busy intervals by start time
        busy_intervals.sort()
        
        # Find free intervals
        free_intervals = []
        prev_end = work_start_min
        for start, end in busy_intervals:
            if start > prev_end:
                free_intervals.append((prev_end, start))
            prev_end = max(prev_end, end)
        if prev_end < work_end_min:
            free_intervals.append((prev_end, work_end_min))
        
        # Check for a free interval that can fit the meeting
        for start, end in free_intervals:
            if end - start >= meeting_duration_min:
                meeting_start = start
                meeting_end = meeting_start + meeting_duration_min
                return (
                    day,
                    f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
                )
    
    return None, None

# Define participants' schedules
participants_schedules = [
    {
        "Monday": ["10:00 to 10:30", "11:30 to 12:00", "13:00 to 13:30", "14:30 to 15:30", "16:00 to 16:30"],
        "Tuesday": ["10:00 to 10:30", "11:00 to 12:00", "14:00 to 16:00", "16:30 to 17:00"],
    },
    {
        "Monday": ["9:00 to 17:00"],
        "Tuesday": ["11:00 to 11:30", "12:00 to 12:30", "13:00 to 14:00", "14:30 to 15:00", "15:30 to 17:00"],
    },
]

# Define constraints
work_hours = "9:00 to 17:00"
meeting_duration = 1  # in hours
days = ["Monday", "Tuesday"]

# Find meeting time
day, time_range = find_meeting_time(participants_schedules, work_hours, meeting_duration, days)

if day and time_range:
    start_time, end_time = time_range.split(':')
    print(f"{day}, {start_time}:{end_time}")
else:
    print("No suitable time found.")