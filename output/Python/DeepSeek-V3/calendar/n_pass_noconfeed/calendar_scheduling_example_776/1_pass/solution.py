def find_meeting_time():
    # Define work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    meeting_duration = 30  # minutes

    # Define days to consider
    days = ['Monday', 'Tuesday', 'Wednesday']

    # Define John's constraints (no meetings, but prefers to avoid Monday after 14:30)
    john_constraints = {
        'Monday': [(14 * 60 + 30, work_end)],  # Avoid after 14:30
        'Tuesday': [(work_start, work_end)],    # Avoid all day
        'Wednesday': [(work_start, work_end)]   # Avoid all day
    }

    # Define Jennifer's meetings (busy times)
    jennifer_schedule = {
        'Monday': [
            (9 * 60, 11 * 60),
            (11 * 60 + 30, 13 * 60),
            (13 * 60 + 30, 14 * 60 + 30),
            (15 * 60, 17 * 60)
        ],
        'Tuesday': [
            (9 * 60, 11 * 60 + 30),
            (12 * 60, 17 * 60)
        ],
        'Wednesday': [
            (9 * 60, 11 * 60 + 30),
            (12 * 60, 12 * 60 + 30),
            (13 * 60, 14 * 60),
            (14 * 60 + 30, 16 * 60),
            (16 * 60 + 30, 17 * 60)
        ]
    }

    # Iterate through each day to find a suitable time
    for day in days:
        # Get John's and Jennifer's busy times for the day
        john_busy = john_constraints.get(day, [])
        jennifer_busy = jennifer_schedule.get(day, [])

        # Combine and sort all busy intervals
        all_busy = john_busy + jennifer_busy
        all_busy.sort()

        # Find free slots by checking gaps between busy intervals
        prev_end = work_start
        free_slots = []

        for start, end in all_busy:
            if start > prev_end:
                free_slots.append((prev_end, start))
            prev_end = max(prev_end, end)

        # Check after the last busy interval
        if prev_end < work_end:
            free_slots.append((prev_end, work_end))

        # Check each free slot for availability
        for slot_start, slot_end in free_slots:
            if slot_end - slot_start >= meeting_duration:
                # Found a suitable slot
                meeting_start = slot_start
                meeting_end = meeting_start + meeting_duration

                # Format the time as HH:MM
                start_hh = meeting_start // 60
                start_mm = meeting_start % 60
                end_hh = meeting_end // 60
                end_mm = meeting_end % 60

                # Return the day and time slot
                return (
                    day,
                    f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}"
                )

    return None  # No slot found (though the problem states one exists)

# Find and print the meeting time
day, time_slot = find_meeting_time()
print(f"{day}: {time_slot}")