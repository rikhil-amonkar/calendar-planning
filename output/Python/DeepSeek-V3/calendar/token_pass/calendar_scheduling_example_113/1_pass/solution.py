def find_meeting_time():
    # Work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    duration = 30        # minutes

    # Busy times in minutes since midnight
    # Format: (start_minute, end_minute)
    bradley_busy = [(9*60+30, 10*60), (12*60+30, 13*60), (13*60+30, 14*60), (15*60+30, 16*60)]
    teresa_busy = [(10*60+30, 11*60), (12*60, 12*60+30), (13*60, 13*60+30), (14*60+30, 15*60)]
    elizabeth_busy = [(9*60, 9*60+30), (10*60+30, 11*60+30), (13*60, 13*60+30), (14*60+30, 15*60), (15*60+30, 17*60)]
    christian_busy = [(9*60, 9*60+30), (10*60+30, 17*60)]

    # Combine all busy times
    all_busy = []
    for busy_list in [bradley_busy, teresa_busy, elizabeth_busy, christian_busy]:
        all_busy.extend(busy_list)

    # Sort by start time
    all_busy.sort(key=lambda x: x[0])

    # Merge overlapping intervals
    merged_busy = []
    for start, end in all_busy:
        if not merged_busy or merged_busy[-1][1] < start:
            merged_busy.append([start, end])
        else:
            merged_busy[-1][1] = max(merged_busy[-1][1], end)

    # Find free slots within work hours
    free_slots = []
    current_time = work_start

    for busy_start, busy_end in merged_busy:
        if busy_start > current_time:
            free_slots.append((current_time, busy_start))
        current_time = max(current_time, busy_end)
    if current_time < work_end:
        free_slots.append((current_time, work_end))

    # Find first slot that fits duration
    for slot_start, slot_end in free_slots:
        if slot_end - slot_start >= duration:
            meeting_start = slot_start
            meeting_end = meeting_start + duration
            # Convert back to HH:MM format
            def to_time_str(minutes):
                h = minutes // 60
                m = minutes % 60
                return f"{h:02d}:{m:02d}"
            return "Monday", to_time_str(meeting_start), to_time_str(meeting_end)

    return None, None, None

if __name__ == "__main__":
    day, start, end = find_meeting_time()
    if day and start and end:
        print(f"{day} {start}:{end}")
    else:
        print("No suitable time found")