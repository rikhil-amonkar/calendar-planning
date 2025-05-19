def find_meeting_time():
    # Define work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes

    # Define participants' busy times in minutes since 9:00
    # Each block is (start, end)
    shirley_busy = [(10*60 + 30, 11*60), (12*60, 12*60 + 30)]
    jacob_busy = [(9*60, 9*60 + 30), (10*60, 10*60 + 30), (11*60, 11*60 + 30),
                  (12*60 + 30, 13*60 + 30), (14*60 + 30, 15*60)]
    stephen_busy = [(11*60 + 30, 12*60), (12*60 + 30, 13*60)]
    margaret_busy = [(9*60, 9*60 + 30), (10*60 + 30, 12*60 + 30),
                     (13*60, 13*60 + 30), (15*60, 15*60 + 30), (16*60 + 30, 17*60)]
    mason_busy = [(9*60, 10*60), (10*60 + 30, 11*60), (11*60 + 30, 12*60 + 30),
                  (13*60, 13*60 + 30), (14*60, 14*60 + 30), (16*60 + 30, 17*60)]

    # Margaret's preference: not before 14:30
    margaret_pref_start = 14 * 60 + 30

    # Combine all busy times
    all_busy = []
    for busy in [shirley_busy, jacob_busy, stephen_busy, margaret_busy, mason_busy]:
        all_busy.extend(busy)

    # Generate free slots by finding gaps between busy times
    all_busy.sort()
    free_slots = []
    prev_end = work_start

    for start, end in all_busy:
        if start > prev_end:
            free_slots.append((prev_end, start))
        prev_end = max(prev_end, end)

    if prev_end < work_end:
        free_slots.append((prev_end, work_end))

    # Check each free slot for availability and Margaret's preference
    meeting_duration = 30
    for slot_start, slot_end in free_slots:
        if slot_end - slot_start >= meeting_duration:
            actual_start = max(slot_start, margaret_pref_start)
            if actual_start + meeting_duration <= slot_end:
                # Convert minutes back to HH:MM format
                start_hh = actual_start // 60
                start_mm = actual_start % 60
                end_hh = (actual_start + meeting_duration) // 60
                end_mm = (actual_start + meeting_duration) % 60
                return f"Monday {start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}"

    return "No suitable time found"

print(find_meeting_time())