def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_free_intervals(busy_intervals, work_start=540, work_end=1020):
    busy_intervals.sort()
    free = []
    prev_end = work_start
    for start, end in busy_intervals:
        if prev_end < start:
            free.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free.append((prev_end, work_end))
    return free

diane_busy = {
    "Monday": [(720, 750), (900, 930)],
    "Tuesday": [(600, 660), (690, 720), (750, 780), (960, 1020)],
    "Wednesday": [(540, 570), (870, 900), (990, 1020)],
    "Thursday": [(930, 990)],
    "Friday": [(570, 690), (870, 900), (960, 1020)]
}

matthew_busy = {
    "Monday": [(540, 600), (630, 1020)],
    "Tuesday": [(540, 1020)],
    "Wednesday": [(540, 660), (720, 870), (960, 1020)],
    "Thursday": [(540, 960)],
    "Friday": [(540, 1020)]
}

days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]

for day in days:
    diane_intervals = get_free_intervals(diane_busy[day])
    matthew_intervals = get_free_intervals(matthew_busy[day])
    for d_start, d_end in diane_intervals:
        for m_start, m_end in matthew_intervals:
            overlap_start = max(d_start, m_start)
            overlap_end = min(d_end, m_end)
            if overlap_start < overlap_end:
                duration = overlap_end - overlap_start
                if duration >= 60:
                    if day == "Wednesday" and overlap_start < 750:
                        continue
                    start_time = minutes_to_time(overlap_start)
                    end_time = minutes_to_time(overlap_end)
                    print(f"{start_time}:{end_time} {day}")
                    exit()