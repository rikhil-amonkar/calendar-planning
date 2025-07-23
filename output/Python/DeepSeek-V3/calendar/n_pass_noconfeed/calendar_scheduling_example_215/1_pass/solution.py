def find_meeting_time(participants_schedules, meeting_duration, work_hours_start, work_hours_end):
    # Convert all time slots to minutes since start of the day for easier calculation
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

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
            start, end = map(time_to_minutes, busy.split(' to '))
            busy_intervals.append((start, end))
    
    # Sort busy intervals by start time
    busy_intervals.sort()

    # Merge overlapping or adjacent busy intervals
    merged = []
    for start, end in busy_intervals:
        if not merged:
            merged.append((start, end))
        else:
            last_start, last_end = merged[-1]
            if start <= last_end:
                new_start = min(last_start, start)
                new_end = max(last_end, end)
                merged[-1] = (new_start, new_end)
            else:
                merged.append((start, end))

    # Find free intervals by inverting the busy intervals
    free_intervals = []
    prev_end = work_start
    for start, end in merged:
        if start > prev_end:
            free_intervals.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free_intervals.append((prev_end, work_end))

    # Find the earliest free interval that can accommodate the meeting
    meeting_duration_min = time_to_minutes(meeting_duration) if isinstance(meeting_duration, str) else meeting_duration
    for start, end in free_intervals:
        if end - start >= meeting_duration_min:
            return (minutes_to_time(start), minutes_to_time(start + meeting_duration_min))
    
    return None

# Define the participants' schedules
participants_schedules = [
    [],  # Steven is free
    [],  # Roy is free
    ["9:30 to 10:30", "11:30 to 12:00", "13:00 to 13:30", "15:00 to 16:00"],  # Cynthia
    ["9:00 to 9:30", "10:30 to 11:00", "11:30 to 12:00", "13:00 to 13:30", "14:00 to 14:30", "15:00 to 15:30", "16:00 to 17:00"],  # Lauren
    ["10:30 to 11:00", "11:30 to 12:00", "12:30 to 13:30", "14:00 to 16:00"],  # Robert
]

# Define meeting duration (30 minutes)
meeting_duration = "0:30"  # or 30 if treated as minutes

# Define work hours
work_hours_start = "9:00"
work_hours_end = "17:00"

# Find the meeting time
meeting_time = find_meeting_time(participants_schedules, meeting_duration, work_hours_start, work_hours_end)

if meeting_time:
    start_time, end_time = meeting_time
    print(f"{start_time}:{end_time}")
    print("Monday")
else:
    print("No suitable time found.")