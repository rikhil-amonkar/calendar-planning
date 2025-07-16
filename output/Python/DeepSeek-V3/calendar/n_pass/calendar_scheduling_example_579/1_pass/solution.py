def find_meeting_time():
    # Define work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes

    # Convert schedules to minutes since midnight
    christine_busy = [
        (11 * 60, 11 * 60 + 30),   # 11:00-11:30
        (15 * 60, 15 * 60 + 30)     # 15:00-15:30
    ]
    
    helen_busy = [
        (9 * 60 + 30, 10 * 60 + 30),  # 9:30-10:30
        (11 * 60, 11 * 60 + 30),       # 11:00-11:30
        (12 * 60, 12 * 60 + 30),       # 12:00-12:30
        (13 * 60 + 30, 16 * 60),       # 13:30-16:00
        (16 * 60 + 30, 17 * 60)        # 16:30-17:00
    ]
    
    # Helen cannot meet after 15:00
    helen_no_meet_after = 15 * 60  # 15:00
    
    meeting_duration = 30  # minutes
    
    # Combine all busy times and sort them
    all_busy = christine_busy + helen_busy
    all_busy.sort()
    
    # Find available slots
    available_slots = []
    prev_end = work_start
    
    for start, end in all_busy:
        if start > prev_end:
            available_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    
    if prev_end < work_end:
        available_slots.append((prev_end, work_end))
    
    # Filter slots based on Helen's constraint and meeting duration
    valid_slots = []
    for slot_start, slot_end in available_slots:
        # Adjust slot_end to not exceed Helen's no-meet-after time
        effective_end = min(slot_end, helen_no_meet_after)
        if effective_end - slot_start >= meeting_duration:
            valid_slots.append((slot_start, effective_end))
    
    # Select the earliest valid slot
    if valid_slots:
        meeting_start = valid_slots[0][0]
        meeting_end = meeting_start + meeting_duration
    else:
        return None
    
    # Convert back to HH:MM format
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"
    
    time_range = f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
    day = "Monday"
    
    return time_range, day

# Run the function and print the result
time_range, day = find_meeting_time()
print(f"{day}: {time_range}")