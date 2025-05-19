def find_meeting_time(participants_schedules, meeting_duration, work_start, work_end, day):
    # Convert time strings to minutes since 9:00 (work_start)
    def time_to_minutes(time_str):
        h, m = map(int, time_str.split(':'))
        return h * 60 + m - work_start_min

    work_start_min = time_to_minutes(work_start)
    work_end_min = time_to_minutes(work_end)
    
    # Initialize a list to track busy intervals for all participants
    busy_intervals = []
    
    for schedule in participants_schedules:
        for busy in schedule:
            start, end = busy
            start_min = time_to_minutes(start)
            end_min = time_to_minutes(end)
            busy_intervals.append((start_min, end_min))
    
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
                new_start = min(last_start, start)
                new_end = max(last_end, end)
                merged[-1] = (new_start, new_end)
            else:
                merged.append((start, end))
    
    # Find available slots between work hours and busy intervals
    available_slots = []
    prev_end = work_start_min
    
    for start, end in merged:
        if start > prev_end:
            available_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    
    if prev_end < work_end_min:
        available_slots.append((prev_end, work_end_min))
    
    # Check each available slot for sufficient duration
    meeting_duration_min = meeting_duration * 60
    for slot_start, slot_end in available_slots:
        if slot_end - slot_start >= meeting_duration_min:
            # Convert back to HH:MM format
            def minutes_to_time(minutes):
                total_min = work_start_min + minutes
                h = total_min // 60
                m = total_min % 60
                return f"{h:02d}:{m:02d}"
            
            meeting_start = minutes_to_time(slot_start)
            meeting_end = minutes_to_time(slot_start + meeting_duration_min)
            return f"{meeting_start}:{meeting_end}", day
    
    return None, day

# Define participants' schedules
participants_schedules = [
    [("13:00", "13:30"), ("16:00", "16:30")],  # Judy
    [("10:00", "10:30"), ("12:00", "13:00"), ("14:00", "14:30")],  # Olivia
    [],  # Eric
    [("10:00", "10:30"), ("15:00", "15:30")],  # Jacqueline
    [("09:00", "10:00"), ("10:30", "12:00"), ("13:00", "13:30"), ("14:30", "15:00"), ("15:30", "17:00")],  # Laura
    [("09:00", "10:00"), ("11:00", "11:30"), ("12:30", "13:00"), ("14:00", "14:30"), ("15:30", "17:00")],  # Tyler
    [("09:30", "10:30"), ("11:00", "11:30"), ("12:00", "12:30"), ("13:00", "13:30"), ("14:00", "14:30"), ("16:00", "17:00")],  # Lisa
]

# Parameters
meeting_duration = 0.5  # 30 minutes
work_start = "09:00"
work_end = "17:00"
day = "Monday"

# Find meeting time
time_range, day = find_meeting_time(participants_schedules, meeting_duration, work_start, work_end, day)
print(f"{time_range} {day}")