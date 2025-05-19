def find_meeting_time():
    # Define work hours and meeting duration
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    meeting_duration = 30  # minutes

    # Participants' schedules and constraints
    schedules = {
        'Wayne': [],
        'Melissa': [(10 * 60, 11 * 60), (12.5 * 60, 14 * 60), (15 * 60, 15.5 * 60)],
        'Catherine': [],
        'Gregory': [(12.5 * 60, 13 * 60), (15.5 * 60, 16 * 60)],
        'Victoria': [(9 * 60, 9.5 * 60), (10.5 * 60, 11.5 * 60), (13 * 60, 14 * 60), (14.5 * 60, 15 * 60), (15.5 * 60, 16.5 * 60)],
        'Thomas': [(10 * 60, 12 * 60), (12.5 * 60, 13 * 60), (14.5 * 60, 16 * 60)],
        'Jennifer': [(9 * 60, 9.5 * 60), (10 * 60, 10.5 * 60), (11 * 60, 13 * 60), (13.5 * 60, 14.5 * 60), (15 * 60, 15.5 * 60), (16 * 60, 16.5 * 60)],
    }

    # Wayne's preference: avoid before 14:00
    wayne_preference_start = 14 * 60

    # Generate busy intervals for all participants except Wayne
    busy_intervals = []
    for person, intervals in schedules.items():
        if person != 'Wayne':
            for interval in intervals:
                busy_intervals.append(interval)

    # Add Wayne's preference as a busy interval if before 14:00
    busy_intervals.append((work_start, wayne_preference_start))

    # Sort busy intervals by start time
    busy_intervals.sort()

    # Find free slots by checking gaps between busy intervals
    free_slots = []
    previous_end = work_start

    for interval in busy_intervals:
        start, end = interval
        if start > previous_end:
            free_slots.append((previous_end, start))
        previous_end = max(previous_end, end)

    # Check the remaining time after the last busy interval
    if previous_end < work_end:
        free_slots.append((previous_end, work_end))

    # Find the first free slot that can accommodate the meeting
    for slot in free_slots:
        start, end = slot
        if end - start >= meeting_duration:
            meeting_start = start
            meeting_end = meeting_start + meeting_duration
            # Format the time as HH:MM:HH:MM
            start_hh = int(meeting_start // 60)
            start_mm = int(meeting_start % 60)
            end_hh = int(meeting_end // 60)
            end_mm = int(meeting_end % 60)
            return f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}"

    return "No suitable time found"

meeting_time = find_meeting_time()
print(f"Monday:{meeting_time}")