def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free_intervals = []
    prev_end = work_start
    for start, end in sorted_busy:
        if start > prev_end:
            free_intervals.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free_intervals.append((prev_end, work_end))
    return free_intervals

def interval_intersection(list1, list2):
    i = 0
    j = 0
    result = []
    while i < len(list1) and j < len(list2):
        a_start, a_end = list1[i]
        b_start, b_end = list2[j]
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            result.append((start, end))
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return result

work_start = 9 * 60
work_end = 17 * 60

participants = {
    'Evelyn': [],
    'Joshua': [(660, 750), (810, 870), (990, 1020)],
    'Kevin': [],
    'Gerald': [],
    'Jerry': [(540, 570), (630, 720), (750, 780), (810, 840), (870, 900), (930, 960)],
    'Jesse': [(540, 570), (630, 720), (750, 780), (870, 900), (930, 990)],
    'Kenneth': [(630, 750), (810, 840), (870, 900), (930, 960), (990, 1020)]
}

free_intervals_list = []
for name in participants:
    busy = participants[name]
    free = get_free_intervals(busy, work_start, work_end)
    free_intervals_list.append(free)

common_intervals = free_intervals_list[0]
for i in range(1, len(free_intervals_list)):
    common_intervals = interval_intersection(common_intervals, free_intervals_list[i])

for interval in common_intervals:
    start, end = interval
    if end - start >= 60:
        start_str = minutes_to_time_str(start)
        end_str = minutes_to_time_str(end)
        print(f"{start_str}:{end_str} Monday")
        break