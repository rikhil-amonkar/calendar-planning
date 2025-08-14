def merge_intervals(intervals):
    if not intervals:
        return []
    sorted_intervals = sorted(intervals, key=lambda x: x[0])
    merged = [sorted_intervals[0]]
    for current in sorted_intervals[1:]:
        last = merged[-1]
        if current[0] <= last[1]:
            merged[-1] = (last[0], max(last[1], current[1]))
        else:
            merged.append(current)
    return merged

def get_free_intervals(busy_intervals, work_start=540, work_end=1020):
    merged = merge_intervals(busy_intervals)
    free = []
    prev_end = work_start
    for interval in merged:
        start, end = interval
        if prev_end < start:
            free.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free.append((prev_end, work_end))
    return free

def find_overlap(A, B):
    i = 0
    j = 0
    overlap = []
    while i < len(A) and j < len(B):
        a_start, a_end = A[i]
        b_start, b_end = B[j]
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            overlap.append((start, end))
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return overlap

eugene_schedule = {
    'Monday': [(660, 720), (810, 840), (870, 900), (960, 990)],
    'Tuesday': [],
    'Wednesday': [(540, 570), (660, 690), (720, 750), (810, 900)],
    'Thursday': [(570, 600), (660, 750)],
    'Friday': [(630, 660), (720, 750), (780, 810)],
}

eric_schedule = {
    'Monday': [(540, 1020)],
    'Tuesday': [(540, 1020)],
    'Wednesday': [(540, 690), (720, 840), (870, 990)],
    'Thursday': [(540, 1020)],
    'Friday': [(540, 660), (690, 1020)],
}

days_order = ['Friday', 'Wednesday', 'Thursday', 'Monday', 'Tuesday']

for day in days_order:
    eric_busy = eric_schedule.get(day, [])
    merged_eric = merge_intervals(eric_busy)
    if merged_eric and merged_eric[0][0] <= 540 and merged_eric[-1][1] >= 1020:
        continue
    eugene_free = get_free_intervals(eugene_schedule.get(day, []))
    eric_free = get_free_intervals(eric_busy)
    overlaps = find_overlap(eugene_free, eric_free)
    for start, end in overlaps:
        if end - start >= 30:
            start_h, start_m = divmod(start, 60)
            end_h, end_m = divmod(end, 60)
            start_str = f"{start_h:02d}:{start_m:02d}"
            end_str = f"{end_h:02d}:{end_m:02d}"
            print(f"{start_str}:{end_str} {day}")
            exit()