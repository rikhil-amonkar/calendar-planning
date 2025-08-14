work_start = 9 * 60
work_end = 17 * 60

# Busy intervals for each participant
stephanie_busy = [(600, 630), (960, 990)]
cheryl_busy = [(600, 630), (690, 720), (810, 840), (990, 1020)]
bradley_busy = [(570, 600), (630, 690), (810, 840), (870, 900), (930, 1020)]
steven_busy = [(540, 720), (780, 810), (870, 1020)]

def get_free_intervals(busy_intervals, work_start, work_end):
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    current_start = work_start
    for s, e in sorted_busy:
        if current_start < s:
            free.append((current_start, s))
        current_start = max(current_start, e)
    if current_start < work_end:
        free.append((current_start, work_end))
    return free

def intersect_intervals(a, b):
    i = 0
    j = 0
    res = []
    while i < len(a) and j < len(b):
        a_start, a_end = a[i]
        b_start, b_end = b[j]
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            res.append((start, end))
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return res

# Compute free intervals for each
stephanie_free = get_free_intervals(stephanie_busy, work_start, work_end)
cheryl_free = get_free_intervals(cheryl_busy, work_start, work_end)
bradley_free = get_free_intervals(bradley_busy, work_start, work_end)
steven_free = get_free_intervals(steven_busy, work_start, work_end)

# Compute common free intervals
common = stephanie_free
common = intersect_intervals(common, cheryl_free)
common = intersect_intervals(common, bradley_free)
common = intersect_intervals(common, steven_free)

# Find the first interval with at least 60 minutes
for start, end in common:
    if end - start >= 60:
        # Convert to time format
        def to_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h:02d}:{m:02d}"
        start_time = to_time(start)
        end_time = to_time(end)
        print(f"{start_time}:{end_time} Monday")
        break