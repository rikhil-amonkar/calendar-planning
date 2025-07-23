def find_meeting_time():
    # Define work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    
    # Define all participants' busy times in minutes (start, end)
    busy_times = {
        'Shirley': [(10 * 60 + 30, 11 * 60), (12 * 60, 12 * 60 + 30)],
        'Jacob': [(9 * 60, 9 * 60 + 30), (10 * 60, 10 * 60 + 30), (11 * 60, 11 * 60 + 30),
                  (12 * 60 + 30, 13 * 60 + 30), (14 * 60 + 30, 15 * 60)],
        'Stephen': [(11 * 60 + 30, 12 * 60), (12 * 60 + 30, 13 * 60)],
        'Margaret': [(9 * 60, 9 * 60 + 30), (10 * 60 + 30, 12 * 60 + 30), (13 * 60, 13 * 60 + 30),
                     (15 * 60, 15 * 60 + 30), (16 * 60 + 30, 17 * 60)],
        'Mason': [(9 * 60, 10 * 60), (10 * 60 + 30, 11 * 60), (11 * 60 + 30, 12 * 60 + 30),
                  (13 * 60, 13 * 60 + 30), (14 * 60, 14 * 60 + 30), (16 * 60 + 30, 17 * 60)],
    }
    
    # Margaret's preference: not before 14:30
    margaret_preference_start = 14 * 60 + 30
    
    # Meeting duration in minutes
    meeting_duration = 30
    
    # Combine all busy times and sort them
    all_busy = []
    for person in busy_times:
        for start, end in busy_times[person]:
            all_busy.append((start, end))
    
    # Add Margaret's preference as a "busy" time before 14:30
    all_busy.append((work_start, margaret_preference_start))
    
    # Sort all busy times by start time
    all_busy.sort()
    
    # Find free slots
    free_slots = []
    prev_end = work_start
    
    for start, end in all_busy:
        if start > prev_end:
            free_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    
    if prev_end < work_end:
        free_slots.append((prev_end, work_end))
    
    # Find the first free slot that can accommodate the meeting
    for slot_start, slot_end in free_slots:
        if slot_end - slot_start >= meeting_duration:
            meeting_start = slot_start
            meeting_end = meeting_start + meeting_duration
            # Convert back to HH:MM format
            start_hh = meeting_start // 60
            start_mm = meeting_start % 60
            end_hh = meeting_end // 60
            end_mm = meeting_end % 60
            # Format as HH:MM:HH:MM
            time_str = f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}"
            return time_str, "Monday"
    
    return None, None

time_range, day = find_meeting_time()
print(f"{{{time_range}}} {day}")