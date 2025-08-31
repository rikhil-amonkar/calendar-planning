def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"


def get_free_intervals(busy_intervals, work_start, work_end):
    free_intervals = []
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    prev_end = work_start
    for start, end in sorted_busy:
        if start > prev_end:
            free_intervals.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free_intervals.append((prev_end, work_end))
    return free_intervals


def find_overlapping_intervals(intervals1, intervals2):
    i = j = 0
    overlaps = []
    while i < len(intervals1) and j < len(intervals2):
        a_start, a_end = intervals1[i]
        b_start, b_end = intervals2[j]
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            overlaps.append((start, end))
            if a_end < b_end:
                i += 1
            else:
                j += 1
        else:
            if a_start < b_start:
                i += 1
            else:
                j += 1
    return overlaps


terry_busy = {
    'Monday': [(630, 660), (750, 840), (900, 1020)],
    'Tuesday': [(570, 600), (630, 660), (840, 870), (960, 990)],
    'Wednesday': [(570, 630), (660, 720), (780, 810), (900, 960), (990, 1020)],
    'Thursday': [(570, 600), (720, 750), (780, 870), (960, 990)],
    'Friday': [(540, 690), (720, 750), (810, 960), (990, 1020)],
}

frances_busy = {
    'Monday': [(570, 660), (690, 780), (840, 870), (900, 960)],
    'Tuesday': [(540, 570), (600, 630), (660, 720), (780, 870), (930, 990)],
    'Wednesday': [(570, 600), (630, 660), (690, 960), (990, 1020)],
    'Thursday': [(660, 750), (870, 1020)],
    'Friday': [(570, 630), (660, 750), (780, 960), (990, 1020)],
}

days_order = ['Monday', 'Wednesday', 'Thursday', 'Friday', 'Tuesday']
work_start = 540  # 9:00 AM
work_end = 1020   # 5:00 PM

for day in days_order:
    terry_intervals = terry_busy.get(day, [])
    frances_intervals = frances_busy.get(day, [])
    terry_free = get_free_intervals(terry_intervals, work_start, work_end)
    frances_free = get_free_intervals(frances_intervals, work_start, work_end)
    overlaps = find_overlapping_intervals(terry_free, frances_free)
    for start, end in overlaps:
        if end - start >= 30:
            earliest_start = start
            earliest_end = earliest_start + 30
            start_time = minutes_to_time(earliest_start)
            end_time = minutes_to_time(earliest_end)
            print(f"{start_time}:{end_time} {day}")
            exit()
