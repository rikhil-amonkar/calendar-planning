def min_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour:02d}:{minute:02d}"

def compute_free(busy_list, work_start, work_end):
    if not busy_list:
        return [(work_start, work_end)]
    busy_list_sorted = sorted(busy_list, key=lambda x: x[0])
    free = []
    current = work_start
    for s, e in busy_list_sorted:
        if current < s:
            free.append((current, s))
        current = max(current, e)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    if not intervals1 or not intervals2:
        return []
    i, j = 0, 0
    result = []
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        start_max = max(start1, start2)
        end_min = min(end1, end2)
        if start_max < end_min:
            result.append((start_max, end_min))
        if end1 < end2:
            i += 1
        else:
            j += 1
    return result

work_start = 540  # 9:00
work_end = 1020   # 17:00

busy_times = {
    "Andrea": [(570, 630), (810, 870)],
    "Ruth": [(750, 780), (900, 930)],
    "Steven": [(600, 630), (660, 690), (720, 750), (810, 840), (900, 960)],
    "Grace": [],
    "Kyle": [(540, 570), (630, 720), (750, 780), (810, 900), (930, 960), (990, 1020)],
    "Elijah": [(540, 660), (690, 780), (810, 840), (930, 960), (990, 1020)],
    "Lori": [(540, 570), (600, 690), (720, 810), (840, 960), (990, 1020)]
}

free_intervals = {}
participants = ['Andrea', 'Ruth', 'Steven', 'Grace', 'Kyle', 'Elijah', 'Lori']
for name in participants:
    free_intervals[name] = compute_free(busy_times[name], work_start, work_end)

common = free_intervals[participants[0]]
for i in range(1, len(participants)):
    common = intersect_intervals(common, free_intervals[participants[i]])
    if not common:
        break

meeting_start = None
for interval in common:
    start, end = interval
    if end - start >= 30:
        meeting_start = start
        meeting_end = meeting_start + 30
        break

start_str = min_to_time(meeting_start)
end_str = min_to_time(meeting_end)
time_range_str = f"{start_str}:{end_str}"

print("Monday")
print(time_range_str)