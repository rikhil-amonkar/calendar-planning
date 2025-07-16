def find_meeting_time():
    # Define work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes

    # Amanda's busy times in minutes (Monday and Tuesday)
    amanda_busy = {
        'Monday': [
            (9 * 60, 10 * 60 + 30),    # 9:00-10:30
            (11 * 60, 11 * 60 + 30),    # 11:00-11:30
            (12 * 60 + 30, 13 * 60),    # 12:30-13:00
            (13 * 60 + 30, 14 * 60),    # 13:30-14:00
            (14 * 60 + 30, 15 * 60),    # 14:30-15:00
        ],
        'Tuesday': [
            (9 * 60, 9 * 60 + 30),     # 9:00-9:30
            (10 * 60, 10 * 60 + 30),    # 10:00-10:30
            (11 * 60 + 30, 12 * 60),    # 11:30-12:00
            (13 * 60 + 30, 14 * 60 + 30),  # 13:30-14:30
            (15 * 60 + 30, 16 * 60),    # 15:30-16:00
            (16 * 60 + 30, 17 * 60),    # 16:30-17:00
        ]
    }

    # Nathan's busy times in minutes (Monday and Tuesday)
    nathan_busy = {
        'Monday': [
            (10 * 60, 10 * 60 + 30),    # 10:00-10:30
            (11 * 60, 11 * 60 + 30),    # 11:00-11:30
            (13 * 60 + 30, 14 * 60 + 30),  # 13:30-14:30
            (16 * 60, 16 * 60 + 30),    # 16:00-16:30
        ],
        'Tuesday': [
            (9 * 60, 10 * 60 + 30),     # 9:00-10:30
            (11 * 60, 13 * 60),         # 11:00-13:00
            (13 * 60 + 30, 14 * 60),    # 13:30-14:00
            (14 * 60 + 30, 15 * 60 + 30),  # 14:30-15:30
            (16 * 60, 16 * 60 + 30),    # 16:00-16:30
        ]
    }

    # Constraints:
    # Amanda does not want to meet on Tuesday after 11:00
    # Nathan cannot meet on Monday

    # Since Nathan cannot meet on Monday, we only check Tuesday
    day = 'Tuesday'

    # Get busy intervals for Amanda and Nathan on Tuesday
    amanda_busy_tuesday = amanda_busy[day]
    nathan_busy_tuesday = nathan_busy[day]

    # Combine and sort all busy intervals
    all_busy = amanda_busy_tuesday + nathan_busy_tuesday
    all_busy.sort()

    # Find free slots by checking gaps between busy intervals
    free_slots = []
    previous_end = work_start

    for start, end in all_busy:
        if start > previous_end:
            free_slots.append((previous_end, start))
        previous_end = max(previous_end, end)

    if previous_end < work_end:
        free_slots.append((previous_end, work_end))

    # Check Amanda's constraint: not after 11:00 on Tuesday
    # So we only consider slots that start before 11:00
    valid_slots = []
    for start, end in free_slots:
        if start < 11 * 60:  # Before 11:00
            slot_start = start
            slot_end = min(end, 11 * 60)  # Cap at 11:00
            if slot_end - slot_start >= meeting_duration:
                valid_slots.append((slot_start, slot_end))

    # Find the first valid slot that fits the meeting duration
    for start, end in valid_slots:
        if end - start >= meeting_duration:
            meeting_start = start
            meeting_end = meeting_start + meeting_duration
            # Convert minutes back to HH:MM format
            def minutes_to_time(minutes):
                hours = minutes // 60
                mins = minutes % 60
                return f"{hours:02d}:{mins:02d}"
            start_time = minutes_to_time(meeting_start)
            end_time = minutes_to_time(meeting_end)
            return f"{day}: {start_time}:{end_time}"

    return "No suitable time found."

# Run the function and print the result
print(find_meeting_time())