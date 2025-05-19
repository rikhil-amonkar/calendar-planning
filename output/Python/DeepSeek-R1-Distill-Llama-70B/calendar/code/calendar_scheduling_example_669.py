def find_meeting_time():
    # Define the work hours in minutes since midnight
    work_start = 9 * 60  # 9:00
    work_end = 17 * 60   # 17:00

    # Define meeting duration in minutes
    meeting_duration = 30  # 30 minutes

    # Jean's busy intervals on Tuesday
    jean_busy_tuesday = [
        (11*60 + 30, 12*60),   # 11:30-12:00
        (16*60, 16*60 + 30)    # 16:00-16:30
    ]

    # Doris's busy intervals on Monday
    doris_busy_monday = [
        (9*60, 11*60 + 30),    # 9:00-11:30
        (12*60, 12*60 + 30),   # 12:00-12:30
        (13*60 + 30, 16*60),   # 13:30-16:00
        (16*60 + 30, 17*60)    # 16:30-17:00
    ]

    # Doris's preference: avoid Monday after 14:00
    doris_preference = 14 * 60  # 14:00

    # Check Monday first
    monday_start = work_start
    monday_end = work_end

    # Generate possible time slots for Monday
    current_time = monday_start
    while current_time < monday_end:
        # Check if current_time is within Doris's preferred time
        if current_time + meeting_duration > doris_preference:
            break  # Doris prefers not to meet after 14:00

        # Check if Jean is available on Monday (Jean has no meetings on Monday)
        # Check if Doris is available at current_time
        doris_available = True
        for busy_start, busy_end in doris_busy_monday:
            if current_time < busy_end and current_time + meeting_duration > busy_start:
                doris_available = False
                break

        if doris_available:
            # Found a suitable time
            start_hour = current_time // 60
            start_minute = current_time % 60
            end_time = current_time + meeting_duration
            end_hour = end_time // 60
            end_minute = end_time % 60
            return f"Monday,{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"

        current_time += 30  # Check every 30 minutes

    # If no time found on Monday, check Tuesday
    tuesday_start = work_start
    tuesday_end = work_end

    current_time = tuesday_start
    while current_time < tuesday_end:
        # Check if Jean is available on Tuesday
        jean_available = True
        for busy_start, busy_end in jean_busy_tuesday:
            if current_time < busy_end and current_time + meeting_duration > busy_start:
                jean_available = False
                break

        if not jean_available:
            current_time += 30  # Skip this time slot
            continue

        # Check if Doris is available on Tuesday
        # Doris is busy all day on Tuesday
        doris_available = False
        for busy_start, busy_end in [(work_start, work_end)]:
            if current_time < busy_end and current_time + meeting_duration > busy_start:
                doris_available = False
                break
        else:
            doris_available = True

        if doris_available:
            start_hour = current_time // 60
            start_minute = current_time % 60
            end_time = current_time + meeting_duration
            end_hour = end_time // 60
            end_minute = end_time % 60
            return f"Tuesday,{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"

        current_time += 30  # Check every 30 minutes

    # If no time found (should not happen as per problem statement)
    return "No available time found"

# Execute the function
print(find_meeting_time())