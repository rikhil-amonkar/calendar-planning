def find_meeting_time():
    start_work = 9 * 60  # 540 minutes
    end_work = 17 * 60   # 1020 minutes

    # Gary's busy intervals
    gary_busy_mon = [(9*60 + 30, 10*60), (11*60, 13*60), (14*60, 14*60 + 30), (16*60 + 30, 17*60)]
    gary_busy_tue = [(9*60, 9*60 + 30), (10*60 + 30, 11*60), (14*60 + 30, 16*60)]

    # David's busy intervals
    david_busy_mon = [(9*60, 9*60 + 30), (10*60, 13*60), (14*60 + 30, 16*60 + 30)]
    david_busy_tue = [(9*60, 9*60 + 30), (10*60, 10*60 + 30), (11*60, 12*60 + 30), (13*60, 14*60 + 30), (15*60, 16*60), (16*60 + 30, 17*60)]

    def get_free_intervals(busy_intervals):
        free_intervals = []
        current_time = start_work
        for start, end in busy_intervals:
            if current_time < start:
                free_intervals.append((current_time, start))
            current_time = max(current_time, end)
        if current_time < end_work:
            free_intervals.append((current_time, end_work))
        return free_intervals

    def find_common_slots(gary_free, david_free):
        common_slots = []
        for g_start, g_end in gary_free:
            for d_start, d_end in david_free:
                start = max(g_start, d_start)
                end = min(g_end, d_end)
                if start < end:
                    common_slots.append((start, end))
        return common_slots

    # Process Monday
    gary_free_mon = get_free_intervals(gary_busy_mon)
    david_free_mon = get_free_intervals(david_busy_mon)
    common_mon = find_common_slots(gary_free_mon, david_free_mon)

    # Process Tuesday
    gary_free_tue = get_free_intervals(gary_busy_tue)
    david_free_tue = get_free_intervals(david_busy_tue)
    common_tue = find_common_slots(gary_free_tue, david_free_tue)

    # Check for valid meeting slots
    days = ['Monday', 'Tuesday']
    for day in days:
        common_slots = common_mon if day == 'Monday' else common_tue
        for slot in common_slots:
            if slot[1] - slot[0] >= 60:
                start_time = slot[0]
                # Convert to HH:MM format for start and end (start + 60)
                start_h = start_time // 60
                start_m = start_time % 60
                end_h = (start_time + 60) // 60
                end_m = (start_time + 60) % 60
                time_str = f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}"
                print(f"{time_str} {day}")
                return

find_meeting_time()