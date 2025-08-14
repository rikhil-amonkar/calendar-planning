def get_free_intervals(work_start, work_end, busy_intervals):
    busy_intervals.sort()
    free = []
    current_start = work_start
    for start, end in busy_intervals:
        if current_start < start:
            free.append([current_start, start])
        current_start = max(current_start, end)
    if current_start < work_end:
        free.append([current_start, work_end])
    return free

def interval_intersection(a, b):
    i = 0
    j = 0
    res = []
    while i < len(a) and j < len(b):
        a1, a2 = a[i]
        b1, b2 = b[j]
        start = max(a1, b1)
        end = min(a2, b2)
        if start < end:
            res.append([start, end])
        if a2 < b2:
            i += 1
        else:
            j += 1
    return res

def apply_frank_constraint(free_intervals, constraint_end):
    constrained = []
    for s, e in free_intervals:
        new_s = max(s, 9 * 60)
        new_e = min(e, constraint_end)
        if new_s < new_e:
            constrained.append([new_s, new_e])
    return constrained

def minutes_to_time_str(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

work_start = 9 * 60
work_end = 17 * 60

busy_emily = [
    [10*60, 10*60 + 30],
    [11*60 + 30, 12*60 + 30],
    [14*60, 15*60],
    [16*60, 16*60 + 30]
]

busy_melissa = [
    [9*60 + 30, 10*60],
    [14*60 + 30, 15*60]
]

busy_frank = [
    [10*60, 10*60 + 30],
    [11*60, 11*60 + 30],
    [12*60 + 30, 13*60],
    [13*60 + 30, 14*60 + 30],
    [15*60, 16*60],
    [16*60 + 30, 17*60]
]

frank_constraint_end = 9*60 + 30  # 570

free_emily = get_free_intervals(work_start, work_end, busy_emily)
free_melissa = get_free_intervals(work_start, work_end, busy_melissa)
free_frank = get_free_intervals(work_start, work_end, busy_frank)

free_frank_constrained = apply_frank_constraint(free_frank, frank_constraint_end)

common_em_mel = interval_intersection(free_emily, free_melissa)
common_all = interval_intersection(common_em_mel, free_frank_constrained)

for interval in common_all:
    start, end = interval
    if end - start >= 30:
        start_str = minutes_to_time_str(start)
        end_str = minutes_to_time_str(end)
        print(f"{start_str}:{end_str} Monday")
        break