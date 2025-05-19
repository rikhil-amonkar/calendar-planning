def find_meeting_time():
    # Define work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes

    # Convert schedules to minutes since midnight
    christine_busy = [
        (11 * 60, 11 * 60 + 30),   # 11:00-11:30
        (15 * 60, 15 * 60 + 30)    # 15:00-15:30
    ]
    
    helen_busy = [
        (9 * 60 + 30, 10 * 60 + 30),  # 9:30-10:30
        (11 * 60, 11 * 60 + 30),      # 11:00-11:30
        (12 * 60, 12 * 60 + 30),      # 12:00-12:30
        (13 * 60 + 30, 16 * 60),      # 13:30-16:00
        (16 * 60 + 30, 17 * 60)       # 16:30-17:00
    ]
    
    # Helen cannot meet after 15:00
    helen_no_meet_after = 15 * 60  # 15:00
    
    meeting_duration = 30  # minutes
    
    # Combine and sort all busy intervals for both participants
    all_busy = christine_busy + helen_busy
    all_busy.sort()
    
    # Find available slots
    available_slots = []
    previous_end = work_start
    
    for start, end in all_busy:
        if start > previous_end:
            available_slots.append((previous_end, start))
        previous_end = max(previous_end, end)
    
    if work_end > previous_end:
        available_slots.append((previous_end, work_end))
    
    # Filter slots that meet all constraints
    valid_slots = []
    for start, end in available_slots:
        # Ensure slot is at least meeting_duration long
        if end - start >= meeting_duration:
            # Ensure Helen can meet (before 15:00)
            slot_end = start + meeting_duration
            if slot_end <= helen_no_meet_after:
                valid_slots.append((start, slot_end))
    
    if not valid_slots:
        return None
    
    # Select the earliest valid slot
    meeting_start, meeting_end = valid_slots[0]
    
    # Convert back to HH:MM format
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"
    
    start_time = minutes_to_time(meeting_start)
    end_time = minutes_to_time(meeting_end)
    
    return f"Monday {start_time}:{end_time}"

# Execute and print the result
print(find_meeting_time())