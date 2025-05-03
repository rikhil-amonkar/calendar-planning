def find_meeting_time():
    # Define work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    meeting_duration = 30  # minutes

    # Define blocked times for Raymond and Gerald on Monday and Tuesday
    # Format: (day, start, end) where day is 0 for Monday, 1 for Tuesday
    raymond_blocked = [
        (0, 9 * 60, 10 * 60),    # Monday 9:00-10:00
        (0, 12 * 60, 12 * 60 + 30),  # Monday 12:00-12:30
        (0, 13 * 60 + 30, 14 * 60 + 30),  # Monday 13:30-14:30
        (0, 16 * 60, 16 * 60 + 30),  # Monday 16:00-16:30
        (1, 9 * 60, 10 * 60 + 30),  # Tuesday 9:00-10:30
        (1, 13 * 60 + 30, 14 * 60 + 30),  # Tuesday 13:30-14:30
        (1, 16 * 60, 16 * 60 + 30),  # Tuesday 16:00-16:30
    ]
    
    gerald_blocked = [
        (0, 9 * 60, 10 * 60 + 30),  # Monday 9:00-10:30
        (0, 11 * 60, 14 * 60),      # Monday 11:00-14:00
        (0, 14 * 60 + 30, 15 * 60), # Monday 14:30-15:00
        (0, 15 * 60 + 30, 17 * 60), # Monday 15:30-17:00
        (1, 9 * 60, 10 * 60 + 30), # Tuesday 9:00-10:30
        (1, 11 * 60, 13 * 60),     # Tuesday 11:00-13:00
        (1, 13 * 60 + 30, 14 * 60 + 30),  # Tuesday 13:30-14:30
        (1, 15 * 60, 17 * 60),      # Tuesday 15:00-17:00
    ]

    # Prefer Monday (day 0) over Tuesday (day 1) due to Raymond's preference
    days_to_check = [0, 1]

    for day in days_to_check:
        # Generate all possible slots for the day
        slots = []
        current_time = work_start
        while current_time + meeting_duration <= work_end:
            slots.append((current_time, current_time + meeting_duration))
            current_time += 1  # Check every minute for availability

        # Check each slot for availability
        for slot_start, slot_end in slots:
            # Check Raymond's availability
            raymond_available = True
            for blocked_day, blocked_start, blocked_end in raymond_blocked:
                if blocked_day == day and not (slot_end <= blocked_start or slot_start >= blocked_end):
                    raymond_available = False
                    break
            
            if not raymond_available:
                continue

            # Check Gerald's availability
            gerald_available = True
            for blocked_day, blocked_start, blocked_end in gerald_blocked:
                if blocked_day == day and not (slot_end <= blocked_start or slot_start >= blocked_end):
                    gerald_available = False
                    break
            
            if gerald_available:
                # Convert minutes back to HH:MM format
                start_hh = slot_start // 60
                start_mm = slot_start % 60
                end_hh = slot_end // 60
                end_mm = slot_end % 60
                return f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}"

    return "No available time found"

# Output the result
print(find_meeting_time())