def get_free_intervals(busy_intervals, work_start, work_end):
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    prev_end = work_start
    for start, end in sorted_busy:
        adjusted_start = max(start, work_start)
        adjusted_end = min(end, work_end)
        if adjusted_start >= adjusted_end:
            continue
        if adjusted_start > prev_end:
            free.append((prev_end, adjusted_start))
        prev_end = max(prev_end, adjusted_end)
    if prev_end < work_end:
        free.append((prev_end, work_end))
    return free

def intersect_intervals(list1, list2):
    i = 0
    j = 0
    result = []
    while i < len(list1) and j < len(list2):
        s1, e1 = list1[i]
        s2, e2 = list2[j]
        os = max(s1, s2)
        oe = min(e1, e2)
        if os < oe:
            result.append((os, oe))
        if e1 < e2:
            i += 1
        else:
            j += 1
    return result

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Busy intervals for each participant
busy_jacqueline = [(540, 570), (660, 690), (750, 780), (930, 960)]
busy_harold = [(600, 630), (780, 810), (900, 1020)]
busy_arthur = [(540, 570), (600, 750), (870, 900), (930, 1020)]
busy_kelly = [(540, 570), (600, 660), (690, 750), (840, 900), (930, 960)]

# Generate free intervals
free_jacqueline = get_free_intervals(busy_jacqueline, 540, 1020)
free_harold = get_free_intervals(busy_harold, 540, 780)
free_arthur = get_free_intervals(busy_arthur, 540, 1020)
free_kelly = get_free_intervals(busy_kelly, 540, 1020)

# Compute intersection
common = free_jacqueline
common = intersect_intervals(common, free_harold)
common = intersect_intervals(common, free_arthur)
common = intersect_intervals(common, free_kelly)

# Find the earliest suitable time
for start, end in common:
    if end - start >= 30:
        start_time = to_time_str(start)
        end_time = to_time_str(start + 30)
        print(f"{start_time}:{end_time}:Monday")
        break