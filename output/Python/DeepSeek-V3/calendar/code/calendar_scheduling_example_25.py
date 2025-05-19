def find_meeting_time():
    # Define work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes

    # Define participants' busy times in minutes since midnight
    anthony_busy = [
        (9 * 60 + 30, 10 * 60),      # 9:30-10:00
        (12 * 60, 13 * 60),           # 12:00-13:00
        (16 * 60, 16 * 60 + 30)      # 16:00-16:30
    ]
    pamela_busy = [
        (9 * 60 + 30, 10 * 60),       # 9:30-10:00
        (16 * 60 + 30, 17 * 60)       # 16:30-17:00
    ]
    zachary_busy = [
        (9 * 60, 11 * 60 + 30),       # 9:00-11:30
        (12 * 60, 12 * 60 + 30),      # 12:00-12:30
        (13 * 60, 13 * 60 + 30),      # 13:00-13:30
        (14 * 60 + 30, 15 * 60),      # 14:30-15:00
        (16 * 60, 17 * 60)            # 16:00-17:00
    ]

    # Pamela's preference: not after 14:30
    pamela_preference_end = 14 * 60 + 30

    # Meeting duration in minutes
    meeting_duration = 60

    # Generate all possible slots
    possible_slots = []
    current_time = work_start

    while current_time + meeting_duration <= work_end:
        slot_end = current_time + meeting_duration
        # Check if the slot is valid for all participants
        anthony_free = all(not (start <= current_time < end or start < slot_end <= end) for start, end in anthony_busy)
        pamela_free = all(not (start <= current_time < end or start < slot_end <= end) for start, end in pamela_busy)
        zachary_free = all(not (start <= current_time < end or start < slot_end <= end) for start, end in zachary_busy)
        # Check Pamela's preference
        pamela_preference_ok = slot_end <= pamela_preference_end

        if anthony_free and pamela_free and zachary_free and pamela_preference_ok:
            possible_slots.append((current_time, slot_end))
        
        current_time += 15  # Check every 15 minutes for efficiency

    if not possible_slots:
        return None

    # Select the first available slot
    chosen_slot = possible_slots[0]
    start_hour = chosen_slot[0] // 60
    start_min = chosen_slot[0] % 60
    end_hour = chosen_slot[1] // 60
    end_min = chosen_slot[1] % 60

    # Format the output
    time_str = f"{start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}"
    return time_str, "Monday"

# Execute and print the result
time_range, day = find_meeting_time()
print(f"{time_range} {day}")