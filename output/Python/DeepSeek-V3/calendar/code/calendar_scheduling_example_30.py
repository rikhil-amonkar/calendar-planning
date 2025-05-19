def find_meeting_time():
    # Define work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes

    # Define participants' busy times in minutes since midnight
    jeffrey_busy = [
        (9 * 60 + 30, 10 * 60),
        (10 * 60 + 30, 11 * 60)
    ]
    virginia_busy = [
        (9 * 60, 9 * 60 + 30),
        (10 * 60, 10 * 60 + 30),
        (14 * 60 + 30, 15 * 60),
        (16 * 60, 16 * 60 + 30)
    ]
    melissa_busy = [
        (9 * 60, 11 * 60 + 30),
        (12 * 60, 12 * 60 + 30),
        (13 * 60, 15 * 60),
        (16 * 60, 17 * 60)
    ]
    melissa_preference_end = 14 * 60  # Prefers not to meet after 14:00

    # Combine all busy times
    all_busy = jeffrey_busy + virginia_busy + melissa_busy

    # Generate available slots (gaps between busy times)
    all_busy.sort()  # Sort by start time
    available_slots = []
    prev_end = work_start

    for start, end in all_busy:
        if start > prev_end:
            available_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        available_slots.append((prev_end, work_end))

    # Filter slots that are at least 30 minutes and meet Melissa's preference
    meeting_duration = 30
    possible_slots = []
    for start, end in available_slots:
        if end - start >= meeting_duration:
            if start < melissa_preference_end:
                possible_slots.append((start, end))

    # Select the earliest possible slot
    if possible_slots:
        chosen_start, chosen_end = possible_slots[0]
        # Convert back to HH:MM format
        start_hh = chosen_start // 60
        start_mm = chosen_start % 60
        end_time = chosen_start + meeting_duration
        end_hh = end_time // 60
        end_mm = end_time % 60
        # Format the output
        time_range = f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}"
        print(f"Monday, {time_range}")
    else:
        print("No suitable time found.")

find_meeting_time()