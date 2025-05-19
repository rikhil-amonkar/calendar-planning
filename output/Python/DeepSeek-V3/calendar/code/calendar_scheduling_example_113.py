def find_meeting_time(participants_schedules, day, work_hours_start, work_hours_end, duration_minutes):
    # Convert time to minutes since start of the day for easier calculation
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
    duration = duration_minutes
    
    # Collect all busy intervals for all participants
    busy_intervals = []
    for schedule in participants_schedules:
        for interval in schedule:
            start, end = map(time_to_minutes, interval.split(' to '))
            busy_intervals.append((start, end))
    
    # Sort all busy intervals by start time
    busy_intervals.sort()
    
    # Merge overlapping or adjacent intervals
    merged = []
    for start, end in busy_intervals:
        if not merged:
            merged.append((start, end))
        else:
            last_start, last_end = merged[-1]
            if start <= last_end:
                # Overlapping or adjacent, merge them
                new_start = min(last_start, start)
                new_end = max(last_end, end)
                merged[-1] = (new_start, new_end)
            else:
                merged.append((start, end))
    
    # Find available slots
    available_slots = []
    prev_end = work_start
    for start, end in merged:
        if start > prev_end:
            available_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        available_slots.append((prev_end, work_end))
    
    # Check each available slot for sufficient duration
    for slot_start, slot_end in available_slots:
        if slot_end - slot_start >= duration:
            meeting_start = slot_start
            meeting_end = meeting_start + duration
            return (minutes_to_time(meeting_start), minutes_to_time(meeting_end))
    
    return None

# Define the participants' schedules
participants_schedules = [
    ["9:30 to 10:00", "12:30 to 13:00", "13:30 to 14:00", "15:30 to 16:00"],  # Bradley
    ["10:30 to 11:00", "12:00 to 12:30", "13:00 to 13:30", "14:30 to 15:00"],  # Teresa
    ["9:00 to 9:30", "10:30 to 11:30", "13:00 to 13:30", "14:30 to 15:00", "15:30 to 17:00"],  # Elizabeth
    ["9:00 to 9:30", "10:30 to 17:00"],  # Christian
]

# Define meeting parameters
day = "Monday"
work_hours_start = "9:00"
work_hours_end = "17:00"
duration_minutes = 30

# Find the meeting time
meeting_time = find_meeting_time(participants_schedules, day, work_hours_start, work_hours_end, duration_minutes)

# Output the result
if meeting_time:
    start_time, end_time = meeting_time
    print(f"{day}: {start_time}:{end_time}")
else:
    print("No suitable time found.")