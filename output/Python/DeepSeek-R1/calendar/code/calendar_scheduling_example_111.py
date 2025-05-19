def time_to_min(t):
    h, m = map(int, t.split(':'))
    return (h - 9) * 60 + m

def min_to_time(m):
    h = 9 + m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

def get_free_intervals(busy_intervals, start=0, end=480):
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    prev_end = start
    for interval in sorted_busy:
        current_start, current_end = interval
        if current_start > prev_end:
            free.append((prev_end, current_start))
        prev_end = max(prev_end, current_end)
    if prev_end < end:
        free.append((prev_end, end))
    return free

def intersect_intervals(a, b):
    i = j = 0
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

gregory_busy = [
    (time_to_min('9:00'), time_to_min('10:00')),
    (time_to_min('10:30'), time_to_min('11:30')),
    (time_to_min('12:30'), time_to_min('13:00')),
    (time_to_min('13:30'), time_to_min('14:00'))
]
natalie_busy = []
christine_busy = [
    (time_to_min('9:00'), time_to_min('11:30')),
    (time_to_min('13:30'), time_to_min('17:00'))
]
vincent_busy = [
    (time_to_min('9:00'), time_to_min('9:30')),
    (time_to_min('10:30'), time_to_min('12:00')),
    (time_to_min('12:30'), time_to_min('14:00')),
    (time_to_min('14:30'), time_to_min('17:00'))
]

gregory_free = get_free_intervals(gregory_busy)
natalie_free = get_free_intervals(natalie_busy)
christine_free = get_free_intervals(christine_busy)
vincent_free = get_free_intervals(vincent_busy)

common_free = gregory_free
common_free = intersect_intervals(common_free, natalie_free)
common_free = intersect_intervals(common_free, christine_free)
common_free = intersect_intervals(common_free, vincent_free)

for interval in common_free:
    start, end = interval
    if end - start >= 30:
        start_time = min_to_time(start)
        end_time = min_to_time(end)
        print(f"Monday {start_time}:{end_time}")
        exit()

print("No suitable time found.")