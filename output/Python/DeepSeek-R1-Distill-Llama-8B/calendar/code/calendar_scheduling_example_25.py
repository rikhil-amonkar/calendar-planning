def find_meeting_time():
    # Define the work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes

    # Define the meeting duration
    meeting_duration = 60  # 1 hour

    # Anthony's busy periods
    anthony_busy = [
        (10 * 60, 11 * 60),   # 9:30-10:00
        (12 * 60, 13 * 60),   # 12:00-13:00
        (16 * 60, 16 * 60 + 30)  # 16:00-16:30
    ]

    # Pamela's busy periods
    pamela_busy = [
        (10 * 60, 11 * 60),    # 9:30-10:00
        (16 * 60 + 30, 17 * 60)  # 16:30-17:00
    ]

    # Zachary's busy periods
    zachary_busy = [
        (9 * 60, 11 * 60 + 30),  # 9:00-11:30
        (12 * 60, 12 * 60 + 30), # 12:00-12:30
        (13 * 60, 13 * 60 + 30), # 13:00-13:30
        (14 * 60 + 30, 15 * 60), # 14:30-15:00
        (16 * 60, 17 * 60)       # 16:00-17:00
    ]

    # Function to check if time is free for a person
    def is_free(busy_times, start, end):
        for b in busy_times:
            if (b[0] <= start < b[1]) or (b[0] <= end - 1 < b[1]):
                return False
        return True

    # Check each possible slot
    for slot in range(work_start, work_end + 1, 60):
        slot_start = slot
        slot_end = slot + meeting_duration
        if slot_end > work_end:
            slot_end = work_end

        # Check if everyone is free
        if is_free(anthony_busy, slot_start, slot_end) and \
           is_free(pamela_busy, slot_start, slot_end) and \
           is_free(zachary_busy, slot_start, slot_end):
            return f"{slot_start:02d}:{slot_end:02d}:Monday"

    return None

# Run the function and print the result
result = find_meeting_time()
if result:
    print(result)
else:
    print("No suitable time found")