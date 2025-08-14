def get_free_intervals(busy_intervals, work_start, work_end):
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free_intervals = []
    prev_end = work_start
    for start, end in sorted_busy:
        if start > prev_end:
            free_intervals.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end <= work_end:
        free_intervals.append((prev_end, work_end))
    return free_intervals

def intersect_intervals(a, b):
    i = 0
    j = 0
    result = []
    while i < len(a) and j < len(b):
        a_start, a_end = a[i]
        b_start, b_end = b[j]
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            result.append((start, end))
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return result

def minutes_to_time(m):
    hours = m // 60
    mins = m % 60
    return f"{hours:02d}:{mins:02d}"

work_start = 9 * 60
work_end = 17 * 60

busy_times = {
    'Kimberly': [
        (10 * 60, 10 * 60 + 30),
        (11 * 60, 12 * 60),
        (16 * 60, 16 * 60 + 30)
    ],
    'Megan': [],
    'Marie': [
        (10 * 60, 11 * 60),
        (11 * 60 + 30, 15 * 60),
        (16 * 60, 16 * 60 + 30)
    ],
    'Diana': [
        (9 * 60 + 30, 10 * 60),
        (10 * 60 + 30, 14 * 60 + 30),
        (15 * 60 + 30, 17 * 60)
    ]
}

free_intervals = {}

for name in busy_times:
    intervals = get_free_intervals(busy_times[name], work_start, work_end)
    if name == 'Megan':
        megan_free = intersect_intervals(intervals, [(10 * 60, work_end)])
        free_intervals[name] = megan_free
    else:
        free_intervals[name] = intervals

common = free_intervals['Kimberly']
for name in ['Megan', 'Marie', 'Diana']:
    common = intersect_intervals(common, free_intervals[name])

for start, end in common:
    if end - start >= 30:
        meeting_start = start
        meeting_end = start + 30
        break

start_time = minutes_to_time(meeting_start)
end_time = minutes_to_time(meeting_end)

print(f"{start_time}:{end_time} Monday")