def find_meeting_time():
    # Define work hours and meeting duration
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    meeting_duration = 30  # minutes

    # Randy's blocked times in minutes (start, end)
    randy_blocked = [
        (9 * 60, 10 * 60 + 30),  # 9:00-10:30
        (11 * 60, 15 * 60 + 30), # 11:00-15:30
        (16 * 60, 17 * 60)        # 16:00-17:00
    ]

    # Evelyn's constraint: no meetings after 13:00
    evelyn_max_time = 13 * 60  # 13:00 in minutes

    # Find available slots for Randy (inverted blocked times)
    randy_available = []
    previous_end = work_start
    for start, end in sorted(randy_blocked):
        if start > previous_end:
            randy_available.append((previous_end, start))
        previous_end = max(previous_end, end)
    if previous_end < work_end:
        randy_available.append((previous_end, work_end))

    # Filter Randy's available slots by Evelyn's constraints
    possible_slots = []
    for start, end in randy_available:
        # Adjust slot to end by 13:00 for Evelyn
        slot_end = min(end, evelyn_max_time)
        if slot_end - start >= meeting_duration:
            possible_slots.append((start, slot_end))

    # Select the earliest possible slot
    if possible_slots:
        chosen_start = possible_slots[0][0]
        chosen_end = chosen_start + meeting_duration
        # Format the time as HH:MM:HH:MM
        start_str = f"{chosen_start // 60:02d}:{chosen_start % 60:02d}"
        end_str = f"{chosen_end // 60:02d}:{chosen_end % 60:02d}"
        print(f"{start_str}:{end_str}")
        print("Monday")
    else:
        print("No available time slot found.")

find_meeting_time()