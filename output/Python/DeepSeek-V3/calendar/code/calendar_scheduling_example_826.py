def find_meeting_time():
    # Define work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    meeting_duration = 30  # minutes

    # Define days to consider (excluding Wednesday and Thursday per Cheryl's preference)
    days = ["Monday", "Tuesday"]

    # James's schedule: each day is a list of busy time slots in minutes since midnight
    james_schedule = {
        "Monday": [
            (9 * 60, 9 * 60 + 30),    # 9:00-9:30
            (10 * 60 + 30, 11 * 60),  # 10:30-11:00
            (12 * 60 + 30, 13 * 60),  # 12:30-13:00
            (14 * 60 + 30, 15 * 60 + 30),  # 14:30-15:30
            (16 * 60 + 30, 17 * 60),  # 16:30-17:00
        ],
        "Tuesday": [
            (9 * 60, 11 * 60),        # 9:00-11:00
            (11 * 60 + 30, 12 * 60),  # 11:30-12:00
            (12 * 60 + 30, 15 * 60 + 30),  # 12:30-15:30
            (16 * 60, 17 * 60),      # 16:00-17:00
        ],
    }

    # Cheryl's schedule is wide open, so only need to check James's schedule

    # Iterate through days in order (Monday, Tuesday)
    for day in days:
        busy_slots = james_schedule.get(day, [])
        # Add boundaries of work hours
        busy_slots.append((work_end, work_end))  # dummy slot to simplify loop

        # Start checking from the beginning of the work day
        prev_end = work_start
        for start, end in busy_slots:
            if start - prev_end >= meeting_duration:
                # Found a suitable slot
                meeting_start = prev_end
                meeting_end = meeting_start + meeting_duration
                # Format the time as HH:MM:HH:MM
                start_hh = meeting_start // 60
                start_mm = meeting_start % 60
                end_hh = meeting_end // 60
                end_mm = meeting_end % 60
                time_str = f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}"
                print(f"{day}: {time_str}")
                return
            prev_end = max(prev_end, end)

    print("No suitable time found.")

find_meeting_time()