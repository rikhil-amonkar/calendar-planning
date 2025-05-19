def find_meeting_time():
    # Define work hours and meeting duration
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    meeting_duration = 30  # minutes

    # Nicole's schedule and preferences
    nicole_busy = [
        (9 * 60, 10 * 60),    # 9:00-10:00
        (10 * 60 + 30, 16 * 60 + 30)  # 10:30-16:30
    ]
    nicole_preferred_start = 16 * 60  # 16:00

    # Judy is free all day, so only Nicole's schedule matters
    potential_slots = []

    # Check time after Nicole's last meeting and before work ends
    last_busy_end = nicole_busy[-1][1]
    if last_busy_end + meeting_duration <= work_end:
        potential_slots.append((last_busy_end, last_busy_end + meeting_duration))

    # Check if preferred time is available (after 16:00)
    if nicole_preferred_start + meeting_duration <= work_end:
        # Check if preferred time is not during a busy slot
        preferred_available = True
        for start, end in nicole_busy:
            if (nicole_preferred_start < end and nicole_preferred_start + meeting_duration > start):
                preferred_available = False
                break
        if preferred_available:
            potential_slots.insert(0, (nicole_preferred_start, nicole_preferred_start + meeting_duration))

    # Select the best available slot (preferred first, then others)
    if potential_slots:
        best_slot = potential_slots[0]
        start_hour = best_slot[0] // 60
        start_min = best_slot[0] % 60
        end_hour = best_slot[1] // 60
        end_min = best_slot[1] % 60
        print(f"{start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}")
        print("Monday")
    else:
        print("No available time slot found.")

find_meeting_time()