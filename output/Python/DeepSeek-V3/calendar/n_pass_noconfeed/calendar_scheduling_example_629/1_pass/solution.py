def find_meeting_time():
    # Define work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes

    # Define the days to consider
    days = ['Monday', 'Tuesday']

    # Define the blocked times for each participant in minutes since start of day
    margaret_blocked = {
        'Monday': [(10 * 60 + 30, 11 * 60), (11 * 60 + 30, 12 * 60), (13 * 60, 13 * 60 + 30), (15 * 60, 17 * 60)],
        'Tuesday': [(12 * 60, 12 * 60 + 30)]
    }
    alexis_blocked = {
        'Monday': [(9 * 60 + 30, 11 * 60 + 30), (12 * 60 + 30, 13 * 60), (14 * 60, 17 * 60)],
        'Tuesday': [(9 * 60, 9 * 60 + 30), (10 * 60, 10 * 60 + 30), (14 * 60, 16 * 60 + 30)]
    }

    # Margaret's constraints: not Monday, not Tuesday before 14:30
    margaret_constraints = {
        'Monday': False,
        'Tuesday': (14 * 60 + 30, work_end)
    }

    # Iterate through each day
    for day in days:
        if day == 'Monday' and not margaret_constraints['Monday']:
            continue  # Skip Monday as per Margaret's preference

        # Get the available time ranges for the day
        available_start = work_start
        available_end = work_end

        # Adjust for Margaret's constraints on Tuesday
        if day == 'Tuesday':
            available_start = max(available_start, margaret_constraints['Tuesday'][0])
            available_end = min(available_end, margaret_constraints['Tuesday'][1])

        # Merge and sort all blocked times for both participants
        all_blocked = margaret_blocked.get(day, []) + alexis_blocked.get(day, [])
        all_blocked.sort()

        # Find available slots
        current_time = available_start
        available_slots = []

        for block_start, block_end in all_blocked:
            if block_start > current_time:
                available_slots.append((current_time, block_start))
            current_time = max(current_time, block_end)

        if current_time < available_end:
            available_slots.append((current_time, available_end))

        # Check each available slot for a meeting
        for slot_start, slot_end in available_slots:
            if slot_end - slot_start >= meeting_duration:
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