def find_meeting_time(participants_schedules, day, work_hours_start, work_hours_end, duration):
    # Convert time strings to minutes since midnight for easier calculations
    def time_to_minutes(time_str):
        hours, minutes = map(int, time_str.split(':'))
        return hours * 60 + minutes
    
    # Convert minutes back to HH:MM format
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"
    
    work_start = time_to_minutes(work_hours_start)
    work_end = time_to_minutes(work_hours_end)
    
    # Initialize a list to keep track of busy intervals for all participants
    busy_intervals = []
    
    for schedule in participants_schedules:
        for busy in schedule:
            start, end = map(time_to_minutes, busy.split(' to '))
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
                new_start = min(last_start, start)
                new_end = max(last_end, end)
                merged[-1] = (new_start, new_end)
            else:
                merged.append((start, end))
    
    # Find available slots by looking at gaps between busy intervals and work hours
    available_slots = []
    prev_end = work_start
    
    for start, end in merged:
        if start > prev_end:
            available_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    
    # Check the time after the last busy interval
    if prev_end < work_end:
        available_slots.append((prev_end, work_end))
    
    # Find the first available slot that can fit the duration
    duration_minutes = duration * 60
    for start, end in available_slots:
        if end - start >= duration_minutes:
            meeting_start = start
            meeting_end = meeting_start + duration_minutes
            return (day, minutes_to_time(meeting_start), minutes_to_time(meeting_end))
    
    return None

# Define participants' schedules
participants_schedules = [
    [],  # Evelyn is free
    ["11:00 to 12:30", "13:30 to 14:30", "16:30 to 17:00"],  # Joshua
    [],  # Kevin is free
    [],  # Gerald is free
    ["09:00 to 09:30", "10:30 to 12:00", "12:30 to 13:00", "13:30 to 14:00", "14:30 to 15:00", "15:30 to 16:00"],  # Jerry
    ["09:00 to 09:30", "10:30 to 12:00", "12:30 to 13:00", "14:30 to 15:00", "15:30 to 16:30"],  # Jesse
    ["10:30 to 12:30", "13:30 to 14:00", "14:30 to 15:00", "15:30 to 16:00", "16:30 to 17:00"],  # Kenneth
]

day = "Monday"
work_hours_start = "09:00"
work_hours_end = "17:00"
duration = 1  # 1 hour

result = find_meeting_time(participants_schedules, day, work_hours_start, work_hours_end, duration)

if result:
    day, start_time, end_time = result
    print(f"{day}: {start_time}:{end_time}")
else:
    print("No suitable time found.")