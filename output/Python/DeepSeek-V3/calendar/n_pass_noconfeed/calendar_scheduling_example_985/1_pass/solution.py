def schedule_meeting():
    # Define work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 60  # 1 hour in minutes

    # Define days to consider
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']

    # Define busy times for each participant per day in minutes since midnight
    diane_busy = {
        'Monday': [(12 * 60, 12 * 60 + 30), (15 * 60, 15 * 60 + 30)],
        'Tuesday': [(10 * 60, 11 * 60), (11 * 60 + 30, 12 * 60), (12 * 60 + 30, 13 * 60), (16 * 60, 17 * 60)],
        'Wednesday': [(9 * 60, 9 * 60 + 30), (14 * 60 + 30, 15 * 60), (16 * 60 + 30, 17 * 60)],
        'Thursday': [(15 * 60 + 30, 16 * 60 + 30)],
        'Friday': [(9 * 60 + 30, 11 * 60 + 30), (14 * 60 + 30, 15 * 60), (16 * 60, 17 * 60)]
    }

    matthew_busy = {
        'Monday': [(9 * 60, 10 * 60), (10 * 60 + 30, 17 * 60)],
        'Tuesday': [(9 * 60, 17 * 60)],
        'Wednesday': [(9 * 60, 11 * 60), (12 * 60, 14 * 60 + 30), (16 * 60, 17 * 60)],
        'Thursday': [(9 * 60, 16 * 60)],
        'Friday': [(9 * 60, 17 * 60)]
    }

    # Matthew's preference: not before 12:30 on Wednesday
    matthew_preference = {
        'Wednesday': 12 * 60 + 30
    }

    # Iterate through each day to find a suitable time
    for day in days:
        # Get busy intervals for both participants
        diane_busy_day = diane_busy.get(day, [])
        matthew_busy_day = matthew_busy.get(day, [])

        # Combine and sort all busy intervals
        all_busy = diane_busy_day + matthew_busy_day
        all_busy.sort()

        # Initialize potential start time
        current_start = work_start

        # Check Matthew's preference for Wednesday
        if day == 'Wednesday':
            current_start = max(current_start, matthew_preference['Wednesday'])

        # Iterate through busy intervals to find a gap
        for start, end in all_busy:
            if current_start + meeting_duration <= start:
                # Found a suitable time
                proposed_start = current_start
                proposed_end = proposed_start + meeting_duration
                # Format the time as HH:MM:HH:MM
                start_hh = proposed_start // 60
                start_mm = proposed_start % 60
                end_hh = proposed_end // 60
                end_mm = proposed_end % 60
                print(f"{day}: {start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}")
                return
            # Update current_start to the end of the current busy interval if it's later
            if end > current_start:
                current_start = end

        # Check the time after the last busy interval
        if current_start + meeting_duration <= work_end:
            proposed_start = current_start
            proposed_end = proposed_start + meeting_duration
            start_hh = proposed_start // 60
            start_mm = proposed_start % 60
            end_hh = proposed_end // 60
            end_mm = proposed_end % 60
            print(f"{day}: {start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}")
            return

    print("No suitable time found.")

schedule_meeting()