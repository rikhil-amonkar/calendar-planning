def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_free_times(busy_intervals, start_work, end_work):
    busy_intervals.sort()
    free = []
    prev_end = start_work
    for start, end in busy_intervals:
        if prev_end < start:
            free.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < end_work:
        free.append((prev_end, end_work))
    return free

def interval_intersection(A, B):
    i = j = 0
    res = []
    while i < len(A) and j < len(B):
        a_start, a_end = A[i]
        b_start, b_end = B[j]
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            res.append((start, end))
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return res

start_work = 9 * 60  # 540 minutes
end_work = 17 * 60   # 1020 minutes

robert_busy = {
    'Monday': [(11*60, 11*60 + 30), (14*60, 14*60 + 30), (15*60 + 30, 16*60)],
    'Tuesday': [(10*60 + 30, 11*60), (15*60, 15*60 + 30)],
    'Wednesday': [(10*60, 11*60), (11*60 + 30, 12*60), (12*60 + 30, 13*60), (13*60 + 30, 14*60), (15*60, 15*60 + 30), (16*60, 16*60 + 30)],
}

ralph_busy = {
    'Monday': [(10*60, 13*60 + 30), (14*60, 14*60 + 30), (15*60, 17*60)],
    'Tuesday': [(9*60, 9*60 + 30), (10*60, 10*60 + 30), (11*60, 11*60 + 30), (12*60, 13*60), (14*60, 15*60 + 30), (16*60, 17*60)],
    'Wednesday': [(10*60 + 30, 11*60), (11*60 + 30, 12*60), (13*60, 14*60 + 30), (16*60 + 30, 17*60)],
}

for day in ['Tuesday', 'Wednesday', 'Monday']:
    robert_b = robert_busy.get(day, [])
    ralph_b = ralph_busy.get(day, [])
    robert_free = get_free_times(robert_b, start_work, end_work)
    ralph_free = get_free_times(ralph_b, start_work, end_work)
    overlaps = interval_intersection(robert_free, ralph_free)
    for (start, end) in overlaps:
        if end - start >= 30:
            start_str = minutes_to_time(start)
            end_str = minutes_to_time(start + 30)
            print(f"{{{start_str}:{end_str}}} {day}")
            exit()