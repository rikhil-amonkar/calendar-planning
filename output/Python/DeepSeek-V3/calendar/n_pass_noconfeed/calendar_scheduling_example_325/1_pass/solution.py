def find_meeting_time():
    # Define work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    meeting_duration = 30  # minutes

    # Define each participant's busy times in minutes since midnight
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

    # Generate all possible time slots
    possible_slots = []
    current_time = work_start
    while current_time + meeting_duration <= work_end:
        slot_end = current_time + meeting_duration
        possible_slots.append((current_time, slot_end))
        current_time += 1  # Check every minute for precision

    # Check each slot against all participants' schedules
    for slot_start, slot_end in possible_slots:
        # Check Jose's constraint
        if slot_start >= jose_constraint:
            continue

        # Check if the slot is free for everyone
        all_free = True
        for person, busy in busy_times.items():
            person_free = True
            for busy_start, busy_end in busy:
                if not (slot_end <= busy_start or slot_start >= busy_end):
                    person_free = False
                    break
            if not person_free:
                all_free = False
                break
        if all_free:
            # Convert minutes back to HH:MM format
            start_hh = slot_start // 60
            start_mm = slot_start % 60
            end_hh = slot_end // 60
            end_mm = slot_end % 60
            return f"Monday {start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}"

    return "No suitable time found"

print(find_meeting_time())