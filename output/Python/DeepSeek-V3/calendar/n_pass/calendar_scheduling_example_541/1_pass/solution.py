def find_meeting_time(participants_schedules, work_hours_start, work_hours_end, duration_minutes):
    # Convert all time strings to minutes since midnight for easier calculation
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
    all_busy_intervals = []
    for schedule in participants_schedules:
        for interval in schedule:
            start, end = map(time_to_minutes, interval.split(':'))
            all_busy_intervals.append((start, end))
    
    # Sort all busy intervals by start time
    all_busy_intervals.sort()
    
    # Merge overlapping or adjacent busy intervals
    merged_intervals = []
    for start, end in all_busy_intervals:
        if not merged_intervals:
            merged_intervals.append([start, end])
        else:
            last_start, last_end = merged_intervals[-1]
            if start <= last_end:
                merged_intervals[-1][1] = max(end, last_end)
            else:
                merged_intervals.append([start, end])
    
    # Find available slots by checking gaps between merged intervals and work hours
    available_slots = []
    prev_end = work_start
    for start, end in merged_intervals:
        if start > prev_end:
            available_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        available_slots.append((prev_end, work_end))
    
    # Check each available slot for a duration that fits the meeting
    for slot_start, slot_end in available_slots:
        if slot_end - slot_start >= duration_minutes:
            meeting_start = slot_start
            meeting_end = meeting_start + duration_minutes
            return (minutes_to_time(meeting_start), minutes_to_time(meeting_end))
    
    return None

# Define the task parameters
participants_schedules = [
    ["10:00:10:30", "14:30:16:00"],  # Kayla's schedule
    ["09:00:13:00", "13:30:15:00", "15:30:16:00"]  # Rebecca's schedule
]
work_hours_start = "09:00"
work_hours_end = "17:00"
duration_minutes = 60  # 1 hour
day_of_week = "Monday"

# Find the meeting time
meeting_time = find_meeting_time(participants_schedules, work_hours_start, work_hours_end, duration_minutes)

# Output the result
if meeting_time:
    start_time, end_time = meeting_time
    print(f"{start_time}:{end_time}")
    print(day_of_week)
else:
    print("No suitable time found.")