def find_meeting_time():
    work_start = 540  # 9:00 in minutes
    work_end = 1020   # 17:00 in minutes

    busy = [
        (540, 570),   # 9:00-9:30
        (630, 720),   # 10:30-12:00
        (750, 810),   # 12:30-13:30
        (840, 870),   # 14:00-14:30
        (900, 990)    # 15:00-16:30
    ]

    busy.sort()
    free_slots = []
    previous_end = work_start

    for interval in busy:
        current_start, current_end = interval
        if current_start > previous_end:
            free_duration = current_start - previous_end
            if free_duration >= 30:
                meeting_start = previous_end
                meeting_end = meeting_start + 30
                free_slots.append((meeting_start, meeting_end))
        previous_end = max(previous_end, current_end)

    # Check after last busy interval
    if previous_end < work_end:
        free_duration = work_end - previous_end
        if free_duration >= 30:
            meeting_start = previous_end
            meeting_end = meeting_start + 30
            free_slots.append((meeting_start, meeting_end))

    # Convert minutes to hours for display
    formatted_slots = []
    for slot in free_slots:
        start_hours = slot[0] // 60
        start_minutes = slot[0] % 60
        end_hours = slot[1] // 60
        end_minutes = slot[1] % 60
        formatted_slots.append(f"{start_hours:02d}:{start_minutes:02d} to {end_hours:02d}:{end_minutes:02d}")

    if formatted_slots:
        # Return the earliest slot
        return formatted_slots[0]
    else:
        return "No available time found."

# Execute the function
meeting_time = find_meeting_time()
print("The best time for the meeting is", meeting_time)
