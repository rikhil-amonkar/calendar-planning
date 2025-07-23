def find_meeting_time():
    # Define work hours and meeting duration
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    meeting_duration = 30  # minutes

    # Evelyn's constraints: available all day but not after 13:00
    evelyn_available_start = work_start
    evelyn_available_end = 13 * 60  # 13:00 in minutes

    # Randy's busy slots in minutes
    randy_busy_slots = [
        (9 * 60, 10 * 60 + 30),   # 9:00-10:30
        (11 * 60, 15 * 60 + 30),  # 11:00-15:30
        (16 * 60, 17 * 60)        # 16:00-17:00
    ]

    # Generate all possible 30-minute slots within Evelyn's availability
    possible_slots = []
    current_time = evelyn_available_start
    while current_time + meeting_duration <= evelyn_available_end:
        slot_start = current_time
        slot_end = current_time + meeting_duration
        possible_slots.append((slot_start, slot_end))
        current_time += 1  # Check every minute

    # Check each slot against Randy's busy times
    for slot_start, slot_end in possible_slots:
        conflict = False
        for busy_start, busy_end in randy_busy_slots:
            if not (slot_end <= busy_start or slot_start >= busy_end):
                conflict = True
                break
        if not conflict:
            # Convert minutes back to HH:MM format
            start_hh = slot_start // 60
            start_mm = slot_start % 60
            end_hh = slot_end // 60
            end_mm = slot_end % 60
            return f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}", "Monday"

    return None, None

# Execute the function
time_range, day = find_meeting_time()
print(f"{time_range}", f"{day}")