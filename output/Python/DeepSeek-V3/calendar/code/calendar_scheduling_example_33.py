def find_meeting_time():
    # Define work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    meeting_duration = 30  # minutes

    # Define each person's busy times in minutes since midnight
    lisa_busy = [
        (9 * 60, 10 * 60),
        (10 * 60 + 30, 11 * 60 + 30),
        (12 * 60 + 30, 13 * 60),
        (16 * 60, 16 * 60 + 30)
    ]
    bobby_busy = [
        (9 * 60, 9 * 60 + 30),
        (10 * 60, 10 * 60 + 30),
        (11 * 60 + 30, 12 * 60),
        (15 * 60, 15 * 60 + 30)
    ]
    randy_busy = [
        (9 * 60 + 30, 10 * 60),
        (10 * 60 + 30, 11 * 60),
        (11 * 60 + 30, 12 * 60 + 30),
        (13 * 60, 13 * 60 + 30),
        (14 * 60 + 30, 15 * 60 + 30),
        (16 * 60, 16 * 60 + 30)
    ]

    # Bobby's preference: avoid after 15:00
    bobby_preference_end = 15 * 60

    # Combine all busy times and sort
    all_busy = lisa_busy + bobby_busy + randy_busy
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

    # Filter slots that are >= meeting_duration and respect Bobby's preference
    valid_slots = []
    for start, end in free_slots:
        if end - start >= meeting_duration:
            # Check if the slot is before Bobby's preference end time or starts before it
            if start < bobby_preference_end:
                valid_start = start
                valid_end = min(end, bobby_preference_end)
                if valid_end - valid_start >= meeting_duration:
                    valid_slots.append((valid_start, valid_end))

    # Select the earliest valid slot
    if valid_slots:
        chosen_start, chosen_end = valid_slots[0]
        # Convert minutes back to HH:MM format
        start_hh = chosen_start // 60
        start_mm = chosen_start % 60
        end_hh = (chosen_start + meeting_duration) // 60
        end_mm = (chosen_start + meeting_duration) % 60

        # Format the output
        time_range = f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}"
        day = "Monday"
        print(f"{time_range}:{day}")
    else:
        print("No suitable time found.")

find_meeting_time()