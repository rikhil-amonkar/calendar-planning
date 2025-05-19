def find_meeting_time():
    # Define the work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes

    # Define the meeting duration
    meeting_duration = 30  # 30 minutes

    # Harold's blocked times on Tuesday
    harold_blocked_tuesday = [
        (9 * 60, 10 * 60),    # 9:00-10:00
        (10 * 60, 11 * 60),  # 10:30-11:00
        (12 * 60, 13 * 60),  # 12:30-13:00
        (14 * 60, 15 * 60),  # 14:30-15:00
        (16 * 60, 17 * 60)   # 16:00-17:00
    ]

    # Find all free slots on Tuesday
    free_slots = []
    for slot in harold_blocked_tuesday:
        start, end = slot
        if start > work_end or end < work_start:
            continue
        free_start = work_start
        free_end = min(end, work_end)
        if free_start < free_end:
            free_slots.append((free_start, free_end))

    # Check if there's a free slot before 14:30
    for slot in free_slots:
        if slot[0] < 14 * 60 and slot[1] > slot[0] + meeting_duration:
            return f"{slot[0]:02d}:{slot[1]:02d}:Tuesday"

    # If no slot found, try the latest possible slot
    latest_slot = max((slot[1] - slot[0] >= meeting_duration for slot in free_slots), default=False)
    if latest_slot:
        latest_slot = [slot for slot in free_slots if slot[1] - slot[0] >= meeting_duration][-1]
        return f"{latest_slot[0]:02d}:{latest_slot[1]:02d}:Tuesday"

    # If no slot found, return None
    return None

# Run the function and print the result
result = find_meeting_time()
if result:
    print(result)
else:
    print("No suitable time found")