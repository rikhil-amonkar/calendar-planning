def find_meeting_time():
    # Define work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    
    # Define participants' busy times in minutes (start, end)
    busy_times = {
        'Jose': [(11 * 60, 11 * 60 + 30), (12 * 60 + 30, 13 * 60)],
        'Keith': [(14 * 60, 14 * 60 + 30), (15 * 60, 15 * 60 + 30)],
        'Logan': [(9 * 60, 10 * 60), (12 * 60, 12 * 60 + 30), (15 * 60, 15 * 60 + 30)],
        'Megan': [(9 * 60, 10 * 60 + 30), (11 * 60, 12 * 60), (13 * 60, 13 * 60 + 30), (14 * 60 + 30, 16 * 60 + 30)],
        'Gary': [(9 * 60, 9 * 60 + 30), (10 * 60, 10 * 60 + 30), (11 * 60 + 30, 13 * 60), (13 * 60 + 30, 14 * 60), (14 * 60 + 30, 16 * 60 + 30)],
        'Bobby': [(11 * 60, 11 * 60 + 30), (12 * 60, 12 * 60 + 30), (13 * 60, 16 * 60)],
    }
    
    # Jose's constraint: not after 15:30
    jose_constraint = 15 * 60 + 30
    
    # Meeting duration in minutes
    meeting_duration = 30
    
    # Collect all busy intervals
    all_busy = []
    for person in busy_times:
        all_busy.extend(busy_times[person])
    
    # Add Jose's constraint as a busy time for everyone
    all_busy.append((jose_constraint, work_end))
    
    # Sort all busy intervals by start time
    all_busy.sort()
    
    # Merge overlapping or adjacent busy intervals
    merged_busy = []
    for start, end in all_busy:
        if not merged_busy:
            merged_busy.append((start, end))
        else:
            last_start, last_end = merged_busy[-1]
            if start <= last_end:
                new_start = min(last_start, start)
                new_end = max(last_end, end)
                merged_busy[-1] = (new_start, new_end))
            else:
                merged_busy.append((start, end))
    
    # Find available slots
    available_slots = []
    previous_end = work_start
    for start, end in merged_busy:
        if start > previous_end:
            available_slots.append((previous_end, start))
        previous_end = max(previous_end, end)
    if previous_end < work_end:
        available_slots.append((previous_end, work_end))
    
    # Filter slots that are at least meeting_duration long
    valid_slots = []
    for start, end in available_slots:
        if end - start >= meeting_duration:
            valid_slots.append((start, end))
    
    # Select the earliest valid slot
    if valid_slots:
        meeting_start = valid_slots[0][0]
        meeting_end = meeting_start + meeting_duration
    else:
        return None
    
    # Convert minutes back to HH:MM format
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"
    
    start_time = minutes_to_time(meeting_start)
    end_time = minutes_to_time(meeting_end)
    
    return f"Monday {start_time}:{end_time}"

# Execute the function and print the result
print(find_meeting_time())