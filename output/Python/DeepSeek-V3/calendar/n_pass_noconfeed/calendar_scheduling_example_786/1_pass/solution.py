def find_meeting_time():
    # Define work hours and days to consider
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    days = ['Monday', 'Tuesday', 'Wednesday']
    meeting_duration = 30  # minutes

    # Define busy times for each person in minutes since midnight
    # Format: {day: [(start1, end1), (start2, end2), ...]}
    amy_busy = {
        'Wednesday': [
            (11 * 60, 11 * 60 + 30),  # 11:00-11:30
            (13 * 60 + 30, 14 * 60)    # 13:30-14:00
        ]
    }

    pamela_busy = {
        'Monday': [
            (9 * 60, 10 * 60 + 30),    # 9:00-10:30
            (11 * 60, 16 * 60 + 30)    # 11:00-16:30
        ],
        'Tuesday': [
            (9 * 60, 9 * 60 + 30),     # 9:00-9:30
            (10 * 60, 17 * 60)         # 10:00-17:00
        ],
        'Wednesday': [
            (9 * 60, 9 * 60 + 30),    # 9:00-9:30
            (10 * 60, 11 * 60),        # 10:00-11:00
            (11 * 60 + 30, 13 * 60 + 30),  # 11:30-13:30
            (14 * 60 + 30, 15 * 60),   # 14:30-15:00
            (16 * 60, 16 * 60 + 30)    # 16:00-16:30
        ]
    }

    # Pamela's preferences: avoid Monday, Tuesday, and Wednesday before 16:00
    # So we prioritize Wednesday after 16:00
    preferred_day = 'Wednesday'
    preferred_start = 16 * 60  # 16:00

    # Check preferred day and time first
    if preferred_day in days:
        # Check if preferred time is available
        start_time = preferred_start
        end_time = start_time + meeting_duration
        if end_time > work_end:
            pass  # Not possible
        else:
            # Check if both are free
            amy_free = True
            pamela_free = True

            # Check Amy's schedule
            if preferred_day in amy_busy:
                for busy_start, busy_end in amy_busy[preferred_day]:
                    if not (end_time <= busy_start or start_time >= busy_end):
                        amy_free = False
                        break

            # Check Pamela's schedule
            if preferred_day in pamela_busy:
                for busy_start, busy_end in pamela_busy[preferred_day]:
                    if not (end_time <= busy_start or start_time >= busy_end):
                        pamela_free = False
                        break

            if amy_free and pamela_free:
                # Format the time as HH:MM:HH:MM
                start_str = f"{start_time // 60:02d}:{start_time % 60:02d}"
                end_str = f"{end_time // 60:02d}:{end_time % 60:02d}"
                print(f"{preferred_day}: {start_str}:{end_str}")
                return

    # If preferred time is not available, check other times
    for day in days:
        # Skip Monday as per Pamela's preference
        if day == 'Monday':
            continue

        # Generate all possible time slots for the day
        current_time = work_start
        while current_time + meeting_duration <= work_end:
            start_time = current_time
            end_time = start_time + meeting_duration

            # Skip if before 16:00 on Wednesday (Pamela's preference)
            if day == 'Wednesday' and end_time <= 16 * 60:
                current_time += 15  # Move in 15-minute increments
                continue

            # Check if both are free
            amy_free = True
            pamela_free = True

            # Check Amy's schedule
            if day in amy_busy:
                for busy_start, busy_end in amy_busy[day]:
                    if not (end_time <= busy_start or start_time >= busy_end):
                        amy_free = False
                        break

            # Check Pamela's schedule
            if day in pamela_busy:
                for busy_start, busy_end in pamela_busy[day]:
                    if not (end_time <= busy_start or start_time >= busy_end):
                        pamela_free = False
                        break

            if amy_free and pamela_free:
                # Format the time as HH:MM:HH:MM
                start_str = f"{start_time // 60:02d}:{start_time % 60:02d}"
                end_str = f"{end_time // 60:02d}:{end_time % 60:02d}"
                print(f"{day}: {start_str}:{end_str}")
                return

            current_time += 15  # Move in 15-minute increments

    print("No suitable time found.")

find_meeting_time()