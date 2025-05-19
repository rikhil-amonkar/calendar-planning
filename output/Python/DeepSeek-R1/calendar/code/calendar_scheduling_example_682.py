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

def get_free_intervals(busy, work_start, work_end):
    merged = merge_intervals(busy)
    free = []
    prev_end = work_start
    for start, end in merged:
        if start > prev_end:
            free.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free.append((prev_end, work_end))
    return free

def to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02}:{mins:02}"

day = "Tuesday"
work_start = 9 * 60
work_end = 11 * 60

amanda_busy = [
    (9 * 60, 9 * 60 + 30),
    (10 * 60, 10 * 60 + 30),
]
nathan_busy = [
    (9 * 60, 10 * 60 + 30),
]

amanda_free = get_free_intervals(amanda_busy, work_start, work_end)
nathan_free = get_free_intervals(nathan_busy, work_start, work_end)

overlap = []
i = j = 0
while i < len(amanda_free) and j < len(nathan_free):
    a_start, a_end = amanda_free[i]
    n_start, n_end = nathan_free[j]
    start = max(a_start, n_start)
    end = min(a_end, n_end)
    if start < end:
        overlap.append((start, end))
    if a_end < n_end:
        i += 1
    else:
        j += 1

for start, end in overlap:
    if end - start >= 30:
        print(f"{day}:{to_time(start)}-{to_time(start + 30)}")
        exit()

print("No suitable time found.")