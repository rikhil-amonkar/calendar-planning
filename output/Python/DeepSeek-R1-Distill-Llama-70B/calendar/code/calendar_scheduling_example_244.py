def find_meeting_time():
    # Define the work hours in minutes and meeting duration
    work_start = 9 * 60
    work_end = 17 * 60
    duration = 30  # 30 minutes

    # Define busy intervals for each participant in minutes
    schedules = {
        "Walter": [],
        "Cynthia": [[9*60, 9*60+30], [10*60, 10*60+30], [13*60+30, 14*60+30], [15*60, 16*60]],
        "Ann": [[10*60, 11*60], [13*60, 13*60+30], [14*60, 15*60], [16*60, 16*60+30]],
        "Catherine": [[9*60, 11*60+30], [12*60+30, 13*60+30], [14*60+30, 17*60]],
        "Kyle": [[9*60, 9*60+30], [10*60, 11*60+30], [12*60, 12*60+30], [13*60, 14*60+30], [15*60, 16*60]]
    }

    # Check each possible time slot
    for time in range(work_start, work_end - duration + 1):
        # Convert time to HH:MM format
        current_time = time
        end_slot = time + duration

        # Check availability for all participants
        available = True
        for person, busy_times in schedules.items():
            for busy_start, busy_end in busy_times:
                # Check if the current slot overlaps with any busy time
                if not (end_slot <= busy_start or current_time >= busy_end):
                    available = False
                    break
            if not available:
                break

        if available:
            # Convert time to HH:MM format
            start_hour = current_time // 60
            start_minute = current_time % 60
            end_hour = end_slot // 60
            end_minute = end_slot % 60

            # Format the output
            return f"{start_hour:02d}:{start_minute:02d}-{end_hour:02d}:{end_minute:02d} on Monday"

    # If no time found (should not happen as per the problem statement)
    return "No available time found"

# Execute the function
meeting_time = find_meeting_time()
print(meeting_time)