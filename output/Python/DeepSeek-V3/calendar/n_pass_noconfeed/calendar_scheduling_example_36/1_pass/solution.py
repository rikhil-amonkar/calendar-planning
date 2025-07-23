def find_meeting_time():
    # Define work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes

    # Define busy intervals for each participant in minutes since midnight
    ryan_busy = [(9 * 60, 9 * 60 + 30), (12 * 60 + 30, 13 * 60)]
    ruth_busy = []  # No meetings
    denise_busy = [(9 * 60 + 30, 10 * 60 + 30), (12 * 60, 13 * 60), (14 * 60 + 30, 16 * 60 + 30)]
    denise_no_meet_after = 12 * 60 + 30  # 12:30 in minutes

    # Combine all busy intervals and sort them
    all_busy = ryan_busy + ruth_busy + denise_busy
    all_busy.sort()

    # Find free intervals by checking gaps between busy intervals and work hours
    free_intervals = []
    previous_end = work_start

    for start, end in all_busy:
        if start > previous_end:
            free_intervals.append((previous_end, start))
        previous_end = max(previous_end, end)

    if previous_end < work_end:
        free_intervals.append((previous_end, work_end))

    # Check each free interval for a 60-minute slot that fits Denise's constraint
    meeting_duration = 60
    suitable_slots = []

    for start, end in free_intervals:
        if end - start >= meeting_duration:
            slot_start = start
            slot_end = slot_start + meeting_duration
            # Ensure the slot doesn't go beyond Denise's no-meet-after time
            if slot_start <= denise_no_meet_after - meeting_duration:
                suitable_slots.append((slot_start, slot_end))

    # Select the earliest suitable slot
    if suitable_slots:
        meeting_start, meeting_end = suitable_slots[0]
    else:
        return None

    # Convert minutes back to HH:MM format
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    start_time = minutes_to_time(meeting_start)
    end_time = minutes_to_time(meeting_end)

    return f"Monday {start_time}:{end_time}"

# Execute and print the result
print(find_meeting_time())