def find_meeting_time(participants_schedules, day, work_start, work_end, duration_minutes):
    # Convert time strings to minutes since 9:00 (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    work_start_min = time_to_minutes(work_start)
    work_end_min = time_to_minutes(work_end)
    duration = duration_minutes
    
    # Initialize a list to track busy intervals for all participants
    busy_intervals = []
    
    for schedule in participants_schedules:
        for interval in schedule:
            start, end = interval
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
                # Overlapping or adjacent, merge them
                new_start = min(last_start, start)
                new_end = max(last_end, end)
                merged[-1] = (new_start, new_end)
            else:
                merged.append((start, end))
    
    # Find available slots by checking gaps between busy intervals and work hours
    available_slots = []
    prev_end = work_start_min
    
    for start, end in merged:
        if start > prev_end:
            available_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    
    # Check the slot after the last busy interval
    if prev_end < work_end_min:
        available_slots.append((prev_end, work_end_min))
    
    # Find the first available slot that can fit the meeting
    for slot_start, slot_end in available_slots:
        if slot_end - slot_start >= duration:
            meeting_start = slot_start
            meeting_end = meeting_start + duration
            # Convert back to HH:MM format
            def minutes_to_time(minutes):
                hh = minutes // 60
                mm = minutes % 60
                return f"{hh:02d}:{mm:02d}"
            
            start_time = minutes_to_time(meeting_start)
            end_time = minutes_to_time(meeting_end)
            return f"{start_time}:{end_time}"
    
    return None

# Define participants' schedules
participants_schedules = [
    [("10:00", "10:30"), ("16:00", "16:30")],  # Emily
    [],                                         # Mason
    [("10:30", "11:00"), ("14:00", "14:30")],  # Maria
    [("09:30", "10:00"), ("10:30", "12:30"), ("13:30", "14:00"), ("14:30", "15:30"), ("16:00", "17:00")],  # Carl
    [("09:30", "11:00"), ("11:30", "12:00"), ("12:30", "13:30"), ("14:00", "15:00"), ("16:00", "17:00")],  # David
    [("09:30", "10:30"), ("11:00", "11:30"), ("12:30", "13:30"), ("14:30", "17:00")]  # Frank
]

# Find meeting time
meeting_time = find_meeting_time(participants_schedules, "Monday", "09:00", "17:00", 30)

# Output the result
print(f"{{{meeting_time}}}")
print("Monday")