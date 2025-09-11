def to_minutes(h, m):
    return h * 60 + m

def to_time_str(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

def get_free_intervals(work_start, work_end, busy_intervals):
    if not busy_intervals:
        return [(work_start, work_end)]
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    merged = []
    current = list(sorted_busy[0])
    for interval in sorted_busy[1:]:
        if interval[0] <= current[1]:
            current[1] = max(current[1], interval[1])
        else:
            merged.append(tuple(current))
            current = list(interval)
    merged.append(tuple(current))
    free = []
    prev_end = work_start
    for interval in merged:
        start, end = interval
        if prev_end < start:
            free.append((prev_end, start))
        prev_end = end
    if prev_end < work_end:
        free.append((prev_end, work_end))
    return free

work_start = 9 * 60
work_end = 17 * 60

# Danielle's busy times
d_busy = [
    (to_minutes(9, 0), to_minutes(10, 0)),
    (to_minutes(10, 30), to_minutes(11, 0)),
    (to_minutes(14, 30), to_minutes(15, 0)),
    (to_minutes(15, 30), to_minutes(16, 0)),
    (to_minutes(16, 30), to_minutes(17, 0)),
]
d_free = get_free_intervals(work_start, work_end, d_busy)

# Bruce's busy times
b_busy = [
    (to_minutes(11, 0), to_minutes(11, 30)),
    (to_minutes(12, 30), to_minutes(13, 0)),
    (to_minutes(14, 0), to_minutes(14, 30)),
    (to_minutes(15, 30), to_minutes(16, 0)),
]
b_free = get_free_intervals(work_start, work_end, b_busy)

# Eric's busy times
e_busy = [
    (to_minutes(9, 0), to_minutes(9, 30)),
    (to_minutes(10, 0), to_minutes(11, 0)),
    (to_minutes(11, 30), to_minutes(13, 0)),
    (to_minutes(14, 30), to_minutes(15, 30)),
]
e_free = get_free_intervals(work_start, work_end, e_busy)

# Find common intervals
for d_s, d_e in d_free:
    for b_s, b_e in b_free:
        overlap_s = max(d_s, b_s)
        overlap_e = min(d_e, b_e)
        if overlap_s < overlap_e:
            for e_s, e_e in e_free:
                common_s = max(overlap_s, e_s)
                common_e = min(overlap_e, e_e)
                if common_s < common_e:
                    duration = common_e - common_s
                    if duration >= 60:
                        start_str = to_time_str(common_s)
                        end_str = to_time_str(common_e)
                        print(f"{start_str}:{end_str} Monday")
                        exit()