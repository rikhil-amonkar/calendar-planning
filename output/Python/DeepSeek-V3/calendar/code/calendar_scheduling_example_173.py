def find_meeting_time():
    # Define work hours and meeting duration
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    meeting_duration = 30  # minutes

    # Define each participant's busy slots in minutes (start, end)
    jacqueline_busy = [
        (9 * 60, 9 * 60 + 30),
        (11 * 60, 11 * 60 + 30),
        (12 * 60 + 30, 13 * 60),
        (15 * 60 + 30, 16 * 60)
    ]
    harold_busy = [
        (10 * 60, 10 * 60 + 30),
        (13 * 60, 13 * 60 + 30),
        (15 * 60, 17 * 60)
    ]
    # Harold doesn't want to meet after 13:00
    harold_no_meet_after = 13 * 60
    arthur_busy = [
        (9 * 60, 9 * 60 + 30),
        (10 * 60, 12 * 60 + 30),
        (14 * 60 + 30, 15 * 60),
        (15 * 60 + 30, 17 * 60)
    ]
    kelly_busy = [
        (9 * 60, 9 * 60 + 30),
        (10 * 60, 11 * 60),
        (11 * 60 + 30, 12 * 60 + 30),
        (14 * 60, 15 * 60),
        (15 * 60 + 30, 16 * 60)
    ]

    # Combine all busy slots for all participants
    all_busy = jacqueline_busy + harold_busy + arthur_busy + kelly_busy

    # Generate free slots by finding gaps in busy times
    all_busy.sort()  # Sort by start time
    free_slots = []
    previous_end = work_start

    for busy_start, busy_end in all_busy:
        if busy_start > previous_end:
            free_slots.append((previous_end, busy_start))
        previous_end = max(previous_end, busy_end)
    if previous_end < work_end:
        free_slots.append((previous_end, work_end))

    # Now, find a free slot that fits the meeting duration and Harold's constraint
    for slot_start, slot_end in free_slots:
        if slot_end - slot_start >= meeting_duration:
            # Check if the slot starts before Harold's no-meet-after time
            potential_start = slot_start
            potential_end = potential_start + meeting_duration
            if potential_end <= harold_no_meet_after:
                # Check if all participants are free during this slot
                all_free = True
                # Check Jacqueline
                for busy_start, busy_end in jacqueline_busy:
                    if busy_start < potential_end and busy_end > potential_start:
                        all_free = False
                        break
                if not all_free:
                    continue
                # Check Harold
                for busy_start, busy_end in harold_busy:
                    if busy_start < potential_end and busy_end > potential_start:
                        all_free = False
                        break
                if not all_free:
                    continue
                # Check Arthur
                for busy_start, busy_end in arthur_busy:
                    if busy_start < potential_end and busy_end > potential_start:
                        all_free = False
                        break
                if not all_free:
                    continue
                # Check Kelly
                for busy_start, busy_end in kelly_busy:
                    if busy_start < potential_end and busy_end > potential_start:
                        all_free = False
                        break
                if all_free:
                    # Format the time as HH:MM:HH:MM
                    start_hh = potential_start // 60
                    start_mm = potential_start % 60
                    end_hh = potential_end // 60
                    end_mm = potential_end % 60
                    time_str = f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}"
                    return time_str, "Monday"

    return "No suitable time found", "Monday"

# Run the function and print the result
time_range, day = find_meeting_time()
print(f"{time_range} {day}")