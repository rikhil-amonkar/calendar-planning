def schedule_meeting():
    # Define work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 60  # minutes

    # Days to check
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]

    # Busy times in minutes since midnight for each day
    # Format: {day: [(start1, end1), (start2, end2), ...]}
    diane_busy = {
        "Monday": [(12*60, 12*60+30), (15*60, 15*60+30)],
        "Tuesday": [(10*60, 11*60), (11*60+30, 12*60), (12*60+30, 13*60), (16*60, 17*60)],
        "Wednesday": [(9*60, 9*60+30), (14*60+30, 15*60), (16*60+30, 17*60)],
        "Thursday": [(15*60+30, 16*60+30)],
        "Friday": [(9*60+30, 11*60+30), (14*60+30, 15*60), (16*60, 17*60)]
    }

    matthew_busy = {
        "Monday": [(9*60, 10*60), (10*60+30, 17*60)],
        "Tuesday": [(9*60, 17*60)],
        "Wednesday": [(9*60, 11*60), (12*60, 14*60+30), (16*60, 17*60)],
        "Thursday": [(9*60, 16*60)],
        "Friday": [(9*60, 17*60)]
    }

    # Check each day
    for day in days:
        # Skip Wednesday before 12:30 per Matthew's preference
        if day == "Wednesday":
            earliest_start = 12*60 + 30
        else:
            earliest_start = work_start

        # Check each possible start time
        for start_min in range(earliest_start, work_end - meeting_duration + 1):
            end_min = start_min + meeting_duration

            # Check if slot is within work hours
            if start_min < work_start or end_min > work_end:
                continue

            # Check Diane's availability
            diane_free = True
            for busy_start, busy_end in diane_busy.get(day, []):
                if not (end_min <= busy_start or start_min >= busy_end):
                    diane_free = False
                    break

            if not diane_free:
                continue

            # Check Matthew's availability
            matthew_free = True
            for busy_start, busy_end in matthew_busy.get(day, []):
                if not (end_min <= busy_start or start_min >= busy_end):
                    matthew_free = False
                    break

            if not matthew_free:
                continue

            # If we get here, both are free for this slot
            # Convert minutes to HH:MM format
            start_hour = start_min // 60
            start_minute = start_min % 60
            end_hour = end_min // 60
            end_minute = end_min % 60

            # Format as HH:MM:HH:MM
            time_range = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
            return day, time_range

    return None, None

# Run the scheduling
day, time_range = schedule_meeting()

if day and time_range:
    print(f"{day}")
    print(f"{time_range}")
else:
    print("No suitable time found")