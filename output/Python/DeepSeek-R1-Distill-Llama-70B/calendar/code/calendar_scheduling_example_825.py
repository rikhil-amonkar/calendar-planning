def find_meeting_time():
    # Define the work hours
    work_hours = {
        "Monday": (9, 17),
        "Tuesday": (9, 17),
        "Wednesday": (9, 17),
        "Thursday": (9, 17)
    }

    # Define busy intervals for Laura and Philip
    laura_busy = {
        "Monday": [(10, 30), (11, 0), (12, 30), (13, 0), (14, 30), (15, 30), (16, 0), (17, 0)],
        "Tuesday": [(9, 30), (10, 0), (11, 0), (11, 30), (13, 0), (13, 30), (14, 30), (15, 0), (16, 0), (17, 0)],
        "Wednesday": [(11, 30), (12, 0), (12, 30), (13, 0), (15, 30), (16, 30)],
        "Thursday": [(10, 30), (11, 0), (12, 0), (13, 30), (15, 0), (15, 30), (16, 0), (16, 30)]
    }

    philip_busy = {
        "Monday": [(9, 0), (17, 0)],
        "Tuesday": [(9, 0), (11, 0), (11, 30), (12, 0), (13, 0), (13, 30), (14, 0), (14, 30), (15, 0), (16, 30)],
        "Wednesday": [(9, 0), (10, 0), (11, 0), (12, 0), (12, 30), (16, 0), (16, 30), (17, 0)],
        "Thursday": [(9, 0), (10, 30), (11, 0), (12, 30), (13, 0), (17, 0)]
    }

    # Philip cannot meet on Wednesday
    days_to_check = ["Monday", "Tuesday", "Thursday"]

    for day in days_to_check:
        start_hour, end_hour = work_hours[day]
        laura_free = []
        current = start_hour
        for busy_start, busy_end in laura_busy[day]:
            if busy_start > current:
                laura_free.append((current, busy_start))
            current = max(current, busy_end)
        if current < end_hour:
            laura_free.append((current, end_hour))

        philip_free = []
        current = start_hour
        for busy_start, busy_end in philip_busy[day]:
            if busy_start > current:
                philip_free.append((current, busy_start))
            current = max(current, busy_end)
        if current < end_hour:
            philip_free.append((current, end_hour))

        common_free = []
        for lf_start, lf_end in laura_free:
            for pf_start, pf_end in philip_free:
                overlap_start = max(lf_start, pf_start)
                overlap_end = min(lf_end, pf_end)
                if overlap_start < overlap_end:
                    common_free.append((overlap_start, overlap_end))

        for slot in common_free:
            start, end = slot
            if end - start >= 1:
                return f"{day} {start:02d}:{start:02d}-{end:02d}:{end:02d}"

    return "No common free time found"

print(find_meeting_time())