def find_meeting_time():
    # Define work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes

    # Define busy intervals in minutes since midnight
    jack_busy = [
        (9 * 60 + 30, 10 * 60 + 30),
        (11 * 60, 11 * 60 + 30),
        (12 * 60 + 30, 13 * 60),
        (14 * 60, 14 * 60 + 30),
        (16 * 60, 16 * 60 + 30)
    ]
    charlotte_busy = [
        (9 * 60 + 30, 10 * 60),
        (10 * 60 + 30, 12 * 60),
        (12 * 60 + 30, 13 * 60 + 30),
        (14 * 60, 16 * 60)
    ]

    # Jack's preference: avoid meetings after 12:30 (12 * 60 + 30)
    jack_preference_end = 12 * 60 + 30

    # Meeting duration in minutes
    meeting_duration = 30

    # Combine and sort all busy intervals
    all_busy = jack_busy + charlotte_busy
    all_busy.sort()

    # Find free slots by checking gaps between busy intervals
    previous_end = work_start
    potential_slots = []

    for start, end in all_busy:
        if start > previous_end:
            # Found a free slot
            potential_slots.append((previous_end, start))
        previous_end = max(previous_end, end)

    # Check the slot after the last busy interval
    if work_end > previous_end:
        potential_slots.append((previous_end, work_end))

    # Filter slots that meet duration and Jack's preference
    valid_slots = []
    for start, end in potential_slots:
        slot_duration = end - start
        if slot_duration >= meeting_duration:
            # Check if the slot starts before Jack's preference end time
            if start + meeting_duration <= jack_preference_end:
                valid_slots.append((start, end))

    # If no valid slots before preference, look after (though not preferred)
    if not valid_slots:
        for start, end in potential_slots:
            slot_duration = end - start
            if slot_duration >= meeting_duration:
                valid_slots.append((start, end))

    # Select the earliest valid slot
    if valid_slots:
        start, end = valid_slots[0]
        meeting_start = start
        meeting_end = start + meeting_duration

        # Convert back to HH:MM format
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