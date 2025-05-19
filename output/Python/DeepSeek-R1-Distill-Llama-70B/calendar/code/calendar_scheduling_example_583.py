def find_meeting_time():
    # Define the work hours in minutes and meeting duration
    work_start = 9 * 60
    work_end = 17 * 60
    duration = 30  # 30 minutes

    # Define busy intervals for each participant in minutes
    lisa_busy = [
        [9*60, 9*60+30],   # 9:00-9:30
        [10*60+30, 11*60], # 10:30-11:00
        [14*60, 16*60]     # 14:00-16:00
    ]

    anthony_busy = [
        [9*60, 9*60+30],   # 9:00-9:30
        [11*60, 11*60+30], # 11:00-11:30
        [12*60+30, 13*60+30], # 12:30-13:30
        [14*60, 15*60],    # 14:00-15:00
        [15*60+30, 16*60], # 15:30-16:00
        [16*60+30, 17*60]  # 16:30-17:00
    ]

    # Combine busy intervals
    all_busy = lisa_busy + anthony_busy

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

            return f"{start_hour:02d}:{start_minute:02d}-{end_hour:02d}:{end_minute:02d} on Monday"

    # If no time found (should not happen as per the problem statement)
    return "No available time found"

# Execute the function
meeting_time = find_meeting_time()
print(meeting_time)