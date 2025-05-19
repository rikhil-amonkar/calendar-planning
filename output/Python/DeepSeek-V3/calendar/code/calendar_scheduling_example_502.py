def find_meeting_time():
    # Define work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes

    # Define busy intervals in minutes since midnight
    jack_busy = [
        (9 * 60 + 30, 10 * 60 + 30),
        (11 * 60, 11 * 60 + 30),
        (12 * 60 + 30, 13 * 60),
        (14 * 60, 14 * 60 + 30),
        (16 * 60, 16 * 60 + 30)
    ]
    charlotte_busy = [
        (9 * 60 + 30, 10 * 60),
        (10 * 60 + 30, 12 * 60),
        (12 * 60 + 30, 13 * 60 + 30),
        (14 * 60, 16 * 60)
    ]

    # Jack prefers no meetings after 12:30
    jack_preference_cutoff = 12 * 60 + 30

    # Combine and sort all busy intervals
    all_busy = jack_busy + charlotte_busy
    all_busy.sort()

    # Find free slots by checking gaps between busy intervals
    free_slots = []
    previous_end = work_start

    for start, end in all_busy:
        if start > previous_end:
            free_slots.append((previous_end, start))
        previous_end = max(previous_end, end)
    
    # Check the slot after the last busy interval
    if previous_end < work_end:
        free_slots.append((previous_end, work_end))

    # Filter slots that are at least 30 minutes and before Jack's preference cutoff
    suitable_slots = []
    for start, end in free_slots:
        if end <= jack_preference_cutoff and (end - start) >= 30:
            suitable_slots.append((start, end))
    
    # If no suitable slots before cutoff, check all free slots
    if not suitable_slots:
        for start, end in free_slots:
            if (end - start) >= 30:
                suitable_slots.append((start, end))
    
    # Select the first suitable slot
    if suitable_slots:
        meeting_start = suitable_slots[0][0]
        meeting_end = meeting_start + 30
    else:
        return "No suitable time found."

    # Convert minutes back to HH:MM format
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    start_time = minutes_to_time(meeting_start)
    end_time = minutes_to_time(meeting_end)

    return f"{start_time}:{end_time}", "Monday"

# Execute and print the result
time_range, day = find_meeting_time()
print(f"{time_range} {day}")