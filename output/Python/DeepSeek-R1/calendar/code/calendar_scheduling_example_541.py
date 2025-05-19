def find_meeting_time():
    work_start = 9 * 60
    work_end = 17 * 60
    duration = 60

    kayla_busy = [(10*60, 10*60+30), (14*60+30, 16*60)]
    rebecca_busy = [(9*60, 13*60), (13*60+30, 15*60), (15*60+30, 16*60)]

    free_slots = []
    current_start = work_start

    # Merge and sort all busy times for both participants
    all_busy = sorted(kayla_busy + rebecca_busy, key=lambda x: x[0])

    for start, end in all_busy:
        if current_start < start:
            free_slots.append((current_start, start))
        current_start = max(current_start, end)
    if current_start < work_end:
        free_slots.append((current_start, work_end))

    # Find first suitable slot
    for slot_start, slot_end in free_slots:
        available_time = slot_end - slot_start
        if available_time >= duration:
            meeting_end = slot_start + duration
            return (
                f"{slot_start//60:02d}:{slot_start%60:02d}:"
                f"{meeting_end//60:02d}:{meeting_end%60:02d}",
                "Monday"
            )

    return None

time_range, day = find_meeting_time()
print(f"{day} {time_range}")