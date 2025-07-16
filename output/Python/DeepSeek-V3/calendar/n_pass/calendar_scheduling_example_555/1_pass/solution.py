def find_meeting_time():
    # Define work hours and meeting duration
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    meeting_duration = 30  # minutes

    # Randy's busy slots in minutes since midnight
    randy_busy = [
        (9 * 60, 10 * 60 + 30),  # 9:00-10:30
        (11 * 60, 15 * 60 + 30),  # 11:00-15:30
        (16 * 60, 17 * 60)        # 16:00-17:00
    ]

    # Evelyn's constraints: no meetings after 13:00
    evelyn_max_end = 13 * 60  # 13:00 in minutes

    # Generate available slots for Randy
    randy_available = []
    previous_end = work_start
    for start, end in randy_busy:
        if start > previous_end:
            randy_available.append((previous_end, start))
        previous_end = end
    if previous_end < work_end:
        randy_available.append((previous_end, work_end))

    # Find overlapping slots that fit Evelyn's constraints
    for r_start, r_end in randy_available:
        # The meeting must start and end within Randy's available slot
        # and end before Evelyn's max time
        slot_start = r_start
        slot_end = min(r_end, evelyn_max_end)

        # Check if there's enough time for the meeting
        if slot_end - slot_start >= meeting_duration:
            meeting_start = slot_start
            meeting_end = meeting_start + meeting_duration
            # Format the time as HH:MM:HH:MM
            start_hh = meeting_start // 60
            start_mm = meeting_start % 60
            end_hh = meeting_end // 60
            end_mm = meeting_end % 60
            return f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}", "Monday"

    return None, None

meeting_time, day = find_meeting_time()
print(f"{meeting_time} {day}")