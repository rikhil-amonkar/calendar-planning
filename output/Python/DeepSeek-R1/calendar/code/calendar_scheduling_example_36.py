work_start = 9 * 60
work_end = 17 * 60

ryan_busy = [(9*60, 9*60 + 30), (12*60 + 30, 13*60)]
ruth_busy = []
denise_busy = [(9*60 + 30, 10*60 + 30), (12*60, 13*60), (14*60 + 30, 16*60 + 30)]

def get_free_intervals(busy, work_start, work_end):
    sorted_busy = sorted(busy, key=lambda x: x[0])
    free = []
    current_start = work_start
    for start, end in sorted_busy:
        if current_start < start:
            free.append((current_start, start))
        current_start = max(current_start, end)
    if current_start < work_end:
        free.append((current_start, work_end))
    return free

ryan_free = get_free_intervals(ryan_busy, work_start, work_end)
ruth_free = get_free_intervals(ruth_busy, work_start, work_end)
denise_free = get_free_intervals(denise_busy, work_start, work_end)

def get_available_starts(free_intervals, constraint_end=None):
    starts = []
    for start, end in free_intervals:
        current_end = min(end, constraint_end) if constraint_end else end
        if current_end - start >= 60:
            starts.extend(range(start, current_end - 60 + 1))
    return starts

ryan_starts = get_available_starts(ryan_free)
ruth_starts = get_available_starts(ruth_free)
denise_starts = get_available_starts(denise_free, 12*60 + 30)

common_starts = set(ryan_starts) & set(ruth_starts) & set(denise_starts)

if common_starts:
    earliest = min(common_starts)
    start_h, start_m = divmod(earliest, 60)
    end_time = earliest + 60
    end_h, end_m = divmod(end_time, 60)
    print(f"Monday {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No suitable time found.")