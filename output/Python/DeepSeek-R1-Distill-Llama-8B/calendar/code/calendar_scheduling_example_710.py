def find_meeting_time():
    # Define the work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes

    # Define the meeting duration
    meeting_duration = 30  # 30 minutes

    # Cheryl's busy periods
    cheryl_busy = [
        (9 * 60, 10 * 60),    # 9:00-10:00
        (11 * 60, 13 * 60),   # 11:30-13:00
        (15 * 60, 16 * 60)    # 15:30-16:00
    ]
    cheryl_busy_tuesday = [
        (15 * 60, 15 * 60 + 30)  # 15:00-15:30
    ]

    # Kyle's busy periods
    kyle_busy = [
        (9 * 60, 17 * 60),           # Monday
        (9 * 60 + 30, 17 * 60),      # Tuesday
        (9 * 60, 9 * 60 + 30),       # Wednesday morning
        (12 * 60, 13 * 60),         # Wednesday mid-morning
        (13 * 60 + 30, 14 * 60),     # Wednesday mid-afternoon
        (14 * 60 + 30, 17 * 60)      # Wednesday late afternoon
    ]

    # Function to check if time is free for a person
    def is_free(busy_times, start, end):
        for b in busy_times:
            if (b[0] <= start < b[1]) or (b[0] <= end - 1 < b[1]):
                return False
        return True

    # Check each day starting from Monday
    for day in ['Monday', 'Tuesday', 'Wednesday']:
        if day == 'Monday':
            # Cheryl is busy on Monday, cannot meet
            continue
        elif day == 'Tuesday':
            # Check if Cheryl is free on Tuesday
            for slot in range(work_start, work_end + 1, 60):
                slot_start = slot
                slot_end = slot + meeting_duration
                if slot_end > work_end:
                    slot_end = work_end
                if is_free(cheryl_busy_tuesday, slot_start, slot_end):
                    if is_free(kyle_busy, slot_start, slot_end):
                        return f"{slot_start:02d}:{slot_end:02d}:{day}"
        elif day == 'Wednesday':
            # Check if Cheryl is free on Wednesday
            for slot in range(work_start, work_end + 1, 60):
                slot_start = slot
                slot_end = slot + meeting_duration
                if slot_end > work_end:
                    slot_end = work_end
                if is_free(cheryl_busy, slot_start, slot_end):
                    if is_free(kyle_busy, slot_start, slot_end):
                        return f"{slot_start:02d}:{slot_end:02d}:{day}"

    return None

# Run the function and print the result
result = find_meeting_time()
if result:
    print(result)
else:
    print("No suitable time found")