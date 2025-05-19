def find_meeting_time():
    # Define the work hours in minutes and meeting duration
    work_start = 9 * 60
    work_end = 17 * 60
    duration = 30  # 30 minutes

    # Define busy intervals for each participant in minutes
    jesse_busy = {
        "Monday": [[13*60 + 30, 14*60], [14*60 + 30, 15*60]],
        "Tuesday": [[9*60, 9*60 + 30], [13*60, 13*60 + 30], [14*60, 15*60]]
    }

    lawrence_busy = {
        "Monday": [[9*60, 17*60]],
        "Tuesday": [[9*60 + 30, 10*60 + 30], [11*60 + 30, 12*60 + 30], 
                    [13*60, 13*60 + 30], [14*60 + 30, 15*60], 
                    [15*60 + 30, 16*60 + 30]]
    }

    # Days to check
    days = ["Monday", "Tuesday"]

    # Lawrence cannot meet on Tuesday after 16:30
    latest_tuesday_start = 16*60 + 30 - duration

    # Iterate through each day
    for day in days:
        # Skip Monday since Lawrence is busy all day
        if day == "Monday":
            continue

        # Get busy intervals for the current day
        jesse_busy_times = jesse_busy.get(day, [])
        lawrence_busy_times = lawrence_busy.get(day, [])

        # Combine busy intervals
        all_busy = jesse_busy_times + lawrence_busy_times

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

            # Additional check for Lawrence's Tuesday constraint
            if day == "Tuesday" and current_time > latest_tuesday_start:
                available = False

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