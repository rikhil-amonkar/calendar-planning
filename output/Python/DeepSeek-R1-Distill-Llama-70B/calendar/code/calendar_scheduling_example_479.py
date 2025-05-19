def find_meeting_time():
    # Define the work hours in minutes and meeting duration
    work_start = 9 * 60
    work_end = 17 * 60
    duration = 60  # 1 hour in minutes

    # Define busy intervals for each participant in minutes
    evelyn_busy = []
    joshua_busy = [[11*60, 12*60+30], [13*60+30, 14*60+30], [16*60+30, 17*60]]
    kevin_busy = []
    gerald_busy = []
    jerry_busy = [
        [9*60, 9*60+30], 
        [10*60+30, 12*60], 
        [12*60+30, 13*60], 
        [13*60+30, 14*60], 
        [14*60+30, 15*60], 
        [15*60+30, 16*60]
    ]
    jesse_busy = [
        [9*60, 9*60+30], 
        [10*60+30, 12*60], 
        [12*60+30, 13*60], 
        [14*60+30, 15*60], 
        [15*60+30, 16*60+30]
    ]
    kenneth_busy = [
        [10*60+30, 12*60+30], 
        [13*60+30, 14*60], 
        [14*60+30, 15*60], 
        [15*60+30, 16*60], 
        [16*60+30, 17*60]
    ]

    # Combine all busy intervals
    all_busy = (
        evelyn_busy + 
        joshua_busy + 
        kevin_busy + 
        gerald_busy + 
        jerry_busy + 
        jesse_busy + 
        kenneth_busy
    )

    # Sort busy intervals by start time
    all_busy.sort(key=lambda x: x[0])

    # Check each possible time slot
    for time in range(work_start, work_end - duration + 1):
        current_time = time
        end_slot = time + duration

        # Check availability for all participants
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