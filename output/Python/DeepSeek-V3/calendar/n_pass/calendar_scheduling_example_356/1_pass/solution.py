def find_meeting_time():
    # Define work hours and meeting duration
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    meeting_duration = 30  # minutes

    # Define each participant's busy times in minutes (start, end)
    katherine_busy = [(12 * 60, 12 * 60 + 30), (13 * 60, 14 * 60 + 30)]
    julie_busy = [(9 * 60, 9 * 60 + 30), (10 * 60 + 30, 11 * 60), (13 * 60 + 30, 14 * 60), (15 * 60, 15 * 60 + 30)]
    angela_busy = [(9 * 60, 10 * 60), (10 * 60 + 30, 11 * 60), (11 * 60 + 30, 14 * 60), (14 * 60 + 30, 15 * 60), (16 * 60 + 30, 17 * 60)]
    nicholas_busy = [(9 * 60 + 30, 11 * 60), (11 * 60 + 30, 13 * 60 + 30), (14 * 60, 16 * 60), (16 * 60 + 30, 17 * 60)]
    carl_busy = [(9 * 60, 11 * 60), (11 * 60 + 30, 12 * 60 + 30), (13 * 60, 14 * 60 + 30), (15 * 60, 16 * 60), (16 * 60 + 30, 17 * 60)]

    # Angela prefers no meetings before 15:00
    angela_preference_start = 15 * 60

    # Combine all busy times
    all_busy = []
    all_busy.extend(katherine_busy)
    all_busy.extend(julie_busy)
    all_busy.extend(angela_busy)
    all_busy.extend(nicholas_busy)
    all_busy.extend(carl_busy)

    # Sort busy intervals by start time
    all_busy.sort()

    # Find free slots by checking gaps between busy intervals and work hours
    free_slots = []
    prev_end = work_start

    for start, end in all_busy:
        if start > prev_end:
            free_slots.append((prev_end, start))
        prev_end = max(prev_end, end)

    # Check the remaining time after the last busy interval
    if prev_end < work_end:
        free_slots.append((prev_end, work_end))

    # Filter free slots that are at least meeting_duration long and meet Angela's preference
    possible_slots = []
    for start, end in free_slots:
        if end - start >= meeting_duration and start >= angela_preference_start:
            possible_slots.append((start, end))

    # Select the earliest possible slot
    if possible_slots:
        meeting_start = possible_slots[0][0]
        meeting_end = meeting_start + meeting_duration
        # Convert minutes back to HH:MM format
        def minutes_to_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"

        start_time = minutes_to_time(meeting_start)
        end_time = minutes_to_time(meeting_end)
        print(f"{start_time}:{end_time}")
        print("Monday")
    else:
        print("No suitable time found.")

find_meeting_time()