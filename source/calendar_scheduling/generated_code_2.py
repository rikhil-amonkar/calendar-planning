def find_meeting_time():
    # Define work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    meeting_duration = 30  # minutes

    # Elijah's busy times and constraints (in minutes)
    elijah_busy = [(9 * 60, 10 * 60)]  # 9:00-10:00
    elijah_no_meet_after = 15 * 60      # 15:00

    # Beverly's busy times (in minutes)
    beverly_busy = [
        (9 * 60, 12.5 * 60),    # 9:00-12:30
        (13.5 * 60, 15.5 * 60), # 13:30-15:30
        (16.5 * 60, 17 * 60)    # 16:30-17:00
    ]

    # Combine all busy intervals for both participants
    all_busy = elijah_busy + beverly_busy
    all_busy.sort()  # Sort by start time

    # Find free slots by checking gaps between busy intervals
    free_slots = []
    previous_end = work_start

    for start, end in all_busy:
        if start > previous_end:
            free_slots.append((previous_end, start))
        previous_end = max(previous_end, end)

    # Add the slot after the last busy interval if any
    if previous_end < work_end:
        free_slots.append((previous_end, work_end))

    # Check each free slot for availability and Elijah's constraint
    for slot_start, slot_end in free_slots:
        # Adjust slot_end to respect Elijah's no-meet-after constraint
        effective_end = min(slot_end, elijah_no_meet_after)
        if effective_end - slot_start >= meeting_duration:
            meeting_start = slot_start
            meeting_end = meeting_start + meeting_duration
            # Format the time as HH:MM:HH:MM
            return f"{int(meeting_start // 60):02d}:{int(meeting_start % 60):02d}:{int(meeting_end // 60):02d}:{int(meeting_end % 60):02d}"

    return "No suitable time found"

print(find_meeting_time())