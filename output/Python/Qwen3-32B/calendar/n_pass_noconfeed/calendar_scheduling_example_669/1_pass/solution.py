def minutes_to_time_str(m):
    hours = m // 60
    mins = m % 60
    return f"{hours:02d}:{mins:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    busy = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    prev_end = work_start
    for start, end in busy:
        if start > prev_end:
            free.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free.append((prev_end, work_end))
    return free

def find_overlapping_intervals(intervals1, intervals2):
    overlaps = []
    for i1 in intervals1:
        for i2 in intervals2:
            start = max(i1[0], i2[0])
            end = min(i1[1], i2[1])
            if start < end:
                overlaps.append((start, end))
    return overlaps

jean_busy = {
    'Monday': [],
    'Tuesday': [(11 * 60 + 30, 12 * 60 + 0), (16 * 60, 16 * 60 + 30)]
}

doris_busy = {
    'Monday': [
        (9 * 60, 11 * 60 + 30),
        (12 * 60, 12 * 60 + 30),
        (13 * 60 + 30, 16 * 60),
        (16 * 60 + 30, 17 * 60)
    ],
    'Tuesday': [(9 * 60, 17 * 60)]
}

work_start = 9 * 60
work_end = 17 * 60

candidates = []

for day in ['Monday', 'Tuesday']:
    jean_intervals = get_free_intervals(jean_busy[day], work_start, work_end)
    doris_intervals = get_free_intervals(doris_busy[day], work_start, work_end)
    overlapping = find_overlapping_intervals(jean_intervals, doris_intervals)
    for s, e in overlapping:
        if e - s >= 30:
            if day == 'Monday' and e > 840:  # 14:00 is 840 minutes
                continue
            start_time = s
            end_time = s + 30
            candidates.append((day, start_time, end_time))

day_order = {'Monday': 0, 'Tuesday': 1}
candidates.sort(key=lambda x: (day_order[x[0]], x[1]))

best = candidates[0]
day = best[0]
start_str = minutes_to_time_str(best[1])
end_str = minutes_to_time_str(best[2])
print(f"{{{start_str}:{end_str}}} {day}")