def find_meeting_time():
    # Define work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes

    # Define each person's busy times in minutes (start, end)
    adam_busy = [(14 * 60, 15 * 60)]
    john_busy = [(13 * 60, 13 * 60 + 30),
                 (14 * 60, 14 * 60 + 30),
                 (15 * 60 + 30, 16 * 60),
                 (16 * 60 + 30, 17 * 60)]
    stephanie_busy = [(9 * 60 + 30, 10 * 60),
                      (10 * 60 + 30, 11 * 60),
                      (11 * 60 + 30, 16 * 60),
                      (16 * 60 + 30, 17 * 60)]
    anna_busy = [(9 * 60 + 30, 10 * 60),
                 (12 * 60, 12 * 60 + 30),
                 (13 * 60, 15 * 60 + 30),
                 (16 * 60 + 30, 17 * 60)]
    
    # Anna's preference: not before 14:30
    anna_preference_start = 14 * 60 + 30

    # Combine all busy times
    all_busy = adam_busy + john_busy + stephanie_busy + anna_busy

    # Generate free slots by finding gaps between busy times
    all_busy.sort()  # Sort by start time
    free_slots = []
    previous_end = work_start

    for busy_start, busy_end in all_busy:
        if busy_start > previous_end:
            free_slots.append((previous_end, busy_start))
        previous_end = max(previous_end, busy_end)
    
    if previous_end < work_end:
        free_slots.append((previous_end, work_end))

    # Filter free slots that meet duration and Anna's preference
    possible_slots = []
    for slot_start, slot_end in free_slots:
        if slot_start >= anna_preference_start and (slot_end - slot_start) >= meeting_duration:
            possible_slots.append((slot_start, slot_end))

    # Select the earliest possible slot
    if possible_slots:
        meeting_start = possible_slots[0][0]
        meeting_end = meeting_start + meeting_duration
        # Convert back to HH:MM format
        start_hh = meeting_start // 60
        start_mm = meeting_start % 60
        end_hh = meeting_end // 60
        end_mm = meeting_end % 60
        print(f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}")
        print("Monday")
    else:
        print("No suitable time found.")

find_meeting_time()