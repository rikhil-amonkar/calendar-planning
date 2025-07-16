def find_meeting_time():
    # Define work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes

    # Define days to consider
    days = ["Monday", "Tuesday"]

    # Define busy slots for each participant per day in minutes since midnight
    jesse_busy = {
        "Monday": [(13 * 60 + 30, 14 * 60), (14 * 60 + 30, 15 * 60)],
        "Tuesday": [(9 * 60, 9 * 60 + 30), (13 * 60, 13 * 60 + 30), (14 * 60, 15 * 60)]
    }

    lawrence_busy = {
        "Monday": [(9 * 60, 17 * 60)],  # Entire day busy
        "Tuesday": [
            (9 * 60 + 30, 10 * 60 + 30),
            (11 * 60 + 30, 12 * 60 + 30),
            (13 * 60, 13 * 60 + 30),
            (14 * 60 + 30, 15 * 60),
            (15 * 60 + 30, 16 * 60 + 30)
        ]
    }

    # Lawrence cannot meet on Tuesday after 16:30
    lawrence_tuesday_cutoff = 16 * 60 + 30

    # Iterate through each day to find a suitable time
    for day in days:
        if day == "Monday":
            # Lawrence is busy all day on Monday
            continue

        # Collect all busy slots for both participants on Tuesday
        busy_slots = jesse_busy[day] + lawrence_busy[day]
        busy_slots.sort()  # Sort by start time

        # Find free slots by checking gaps between busy slots and work hours
        prev_end = work_start
        free_slots = []

        for start, end in busy_slots:
            if start > prev_end:
                free_slots.append((prev_end, start))
            prev_end = max(prev_end, end)

        # Check after last busy slot
        if prev_end < work_end and day == "Tuesday":
            # Apply Lawrence's cutoff on Tuesday
            latest_end = min(work_end, lawrence_tuesday_cutoff)
            if prev_end < latest_end:
                free_slots.append((prev_end, latest_end))

        # Check each free slot for availability
        for slot_start, slot_end in free_slots:
            slot_duration = slot_end - slot_start
            if slot_duration >= meeting_duration:
                meeting_start = slot_start
                meeting_end = meeting_start + meeting_duration
                # Format the time as HH:MM:HH:MM
                start_hh = meeting_start // 60
                start_mm = meeting_start % 60
                end_hh = meeting_end // 60
                end_mm = meeting_end % 60
                time_str = f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}"
                return day, time_str

    return None, None

day, time_str = find_meeting_time()
print(f"{day}: {time_str}")