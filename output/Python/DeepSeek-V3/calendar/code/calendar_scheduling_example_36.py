def find_meeting_time():
    # Define work hours and meeting duration
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    meeting_duration = 60  # 1 hour in minutes

    # Define busy slots for each participant in minutes since midnight
    ryan_busy = [
        (9 * 60, 9 * 60 + 30),   # 9:00-9:30
        (12 * 60 + 30, 13 * 60)  # 12:30-13:00
    ]
    ruth_busy = []  # No meetings
    denise_busy = [
        (9 * 60 + 30, 10 * 60 + 30),  # 9:30-10:30
        (12 * 60, 13 * 60),            # 12:00-13:00
        (14 * 60 + 30, 16 * 60 + 30)   # 14:30-16:30
    ]
    denise_no_meet_after = 12 * 60 + 30  # 12:30

    # Combine all busy slots
    all_busy = ryan_busy + ruth_busy + denise_busy

    # Sort busy slots by start time
    all_busy.sort()

    # Find available slots
    available_slots = []
    prev_end = work_start

    for busy_start, busy_end in all_busy:
        if busy_start > prev_end:
            available_slots.append((prev_end, busy_start))
        prev_end = max(prev_end, busy_end)

    if prev_end < work_end:
        available_slots.append((prev_end, work_end))

    # Filter slots that meet duration and Denise's constraint
    valid_slots = []
    for slot_start, slot_end in available_slots:
        if slot_end - slot_start >= meeting_duration:
            # Check if slot starts before Denise's no-meet-after time
            if slot_start <= denise_no_meet_after:
                valid_slots.append((slot_start, slot_end))

    # Select the earliest valid slot
    if valid_slots:
        meeting_start = valid_slots[0][0]
        meeting_end = meeting_start + meeting_duration
    else:
        return None

    # Convert minutes back to HH:MM format
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    start_time = minutes_to_time(meeting_start)
    end_time = minutes_to_time(meeting_end)

    return f"{start_time}:{end_time}", "Monday"

# Execute and print the result
meeting_time, day = find_meeting_time()
print(f"{{{meeting_time}}} {day}")