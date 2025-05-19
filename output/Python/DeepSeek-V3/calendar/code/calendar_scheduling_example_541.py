def find_meeting_time(participants_schedules, work_hours_start, work_hours_end, duration_minutes, day):
    # Convert all time strings to minutes since midnight for easier calculation
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
    for schedule in participents_schedules:
        for interval in schedule:
            start, end = map(time_to_minutes, interval.split(' to '))
            busy_intervals.append((start, end))
    
    # Sort all busy intervals by start time
    busy_intervals.sort()
    
    # Find available slots by merging busy intervals
    available_slots = []
    prev_end = work_start
    
    for start, end in busy_intervals:
        if start > prev_end:
            available_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    
    if prev_end < work_end:
        available_slots.append((prev_end, work_end))
    
    # Check each available slot for sufficient duration
    for slot in available_slots:
        slot_start, slot_end = slot
        if slot_end - slot_start >= duration_minutes:
            meeting_start = slot_start
            meeting_end = meeting_start + duration_minutes
            return (minutes_to_time(meeting_start), minutes_to_time(meeting_end))
    
    return None

# Define the problem parameters
participants_schedules = [
    ["10:00 to 10:30", "14:30 to 16:00"],  # Kayla's schedule
    ["09:00 to 13:00", "13:30 to 15:00", "15:30 to 16:00"]  # Rebecca's schedule
]
work_hours_start = "09:00"
work_hours_end = "17:00"
duration_minutes = 60
day = "Monday"

# Find the meeting time
meeting_time = find_meeting_time(participants_schedules, work_hours_start, work_hours_end, duration_minutes, day)

# Output the result
if meeting_time:
    start_time, end_time = meeting_time
    print(f"{start_time}:{end_time}")
    print(day)
else:
    print("No suitable meeting time found.")