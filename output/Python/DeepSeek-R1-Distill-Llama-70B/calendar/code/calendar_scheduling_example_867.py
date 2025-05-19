def find_meeting_time():
    # Define the work hours in minutes and meeting duration
    work_start = 9 * 60
    work_end = 17 * 60
    duration = 30  # 30 minutes

    # Define busy intervals for each participant in minutes
    betty_busy = {
        "Monday": [[10*60, 10*60+30], [13*60+30, 14*60], [15*60, 15*60+30], [16*60, 16*60+30]],
        "Tuesday": [[9*60, 9*60+30], [11*60+30, 12*60], [12*60+30, 13*60], [13*60+30, 14*60], [16*60+30, 17*60]],
        "Wednesday": [[9*60+30, 10*60+30], [13*60, 13*60+30], [14*60, 14*60+30]],
        "Thursday": [[9*60+30, 10*60], [11*60+30, 12*60], [14*60, 14*60+30], [15*60, 15*60+30], [16*60+30, 17*60]]
    }

    scott_busy = {
        "Monday": [[9*60+30, 15*60], [15*60+30, 16*60], [16*60+30, 17*60]],
        "Tuesday": [[9*60, 9*60+30], [10*60, 11*60], [11*60+30, 12*60], [12*60+30, 13*60+30], [14*60, 15*60], [16*60, 16*60+30]],
        "Wednesday": [[9*60+30, 12*60+30], [13*60, 13*60+30], [14*60, 14*60+30], [15*60, 15*60+30], [16*60, 16*60+30]],
        "Thursday": [[9*60, 9*60+30], [10*60, 10*60+30], [11*60, 12*60], [12*60+30, 13*60], [15*60, 16*60], [16*60+30, 17*60]]
    }

    # Days to check (Betty cannot meet on Monday, Tuesday, or Thursday before 15:00)
    days = ["Wednesday", "Thursday"]

    # Scott's preference to avoid meetings on Wednesday
    # We'll prioritize Thursday first

    # Check Thursday first
    day = "Thursday"
    # Only consider times after 15:00 (Betty's constraint)
    start_time = max(work_start, 15*60)  # 15:00 in minutes

    # Get busy intervals for the current day
    betty_busy_times = betty_busy.get(day, [])
    scott_busy_times = scott_busy.get(day, [])

    # Combine busy intervals
    all_busy = betty_busy_times + scott_busy_times

    # Sort busy intervals by start time
    all_busy.sort(key=lambda x: x[0])

    # Check each possible time slot after 15:00
    for time in range(start_time, work_end - duration + 1):
        current_time = time
        end_slot = time + duration

        # Check availability for both participants
        available = True
        for busy_start, busy_end in all_busy:
            if not (end_slot <= busy_start or current_time >= busy_end):
                available = False
                break

        if available:
            # Convert time to HH:MM format
            start_hour = current_time // 60
            start_minute = current_time % 60
            end_hour = end_slot // 60
            end_minute = end_slot % 60

            return f"{start_hour:02d}:{start_minute:02d}-{end_hour:02d}:{end_minute:02d} on {day}"

    # If no time found on Thursday, check Wednesday (though Scott prefers to avoid it)
    day = "Wednesday"
    # Get busy intervals for the current day
    betty_busy_times = betty_busy.get(day, [])
    scott_busy_times = scott_busy.get(day, [])

    # Combine busy intervals
    all_busy = betty_busy_times + scott_busy_times

    # Sort busy intervals by start time
    all_busy.sort(key=lambda x: x[0])

    # Check each possible time slot
    for time in range(work_start, work_end - duration + 1):
        current_time = time
        end_slot = time + duration

        # Check availability for both participants
        available = True
        for busy_start, busy_end in all_busy:
            if not (end_slot <= busy_start or current_time >= busy_end):
                available = False
                break

        if available:
            # Convert time to HH:MM format
            start_hour = current_time // 60
            start_minute = current_time % 60
            end_hour = end_slot // 60
            end_minute = end_slot % 60

            return f"{start_hour:02d}:{start_minute:02d}-{end_hour:02d}:{end_minute:02d} on {day}"

    # If no time found (should not happen as per the problem statement)
    return "No available time found"

# Execute the function
meeting_time = find_meeting_time()
print(meeting_time)