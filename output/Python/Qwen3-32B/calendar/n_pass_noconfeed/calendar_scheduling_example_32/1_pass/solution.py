def minutes_to_time(minutes):
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

# Define work hours
work_start = 9 * 60  # 540 minutes
work_end = 17 * 60   # 1020 minutes

# Emily's busy intervals
emily_busy = [
    (10 * 60, 10 * 60 + 30),  # 10:00-10:30
    (11 * 60 + 30, 12 * 60 + 30),  # 11:30-12:30
    (14 * 60, 15 * 60),  # 14:00-15:00
    (16 * 60, 16 * 60 + 30)  # 16:00-16:30
]
emily_free = get_free_intervals(emily_busy, work_start, work_end)

# Melissa's busy intervals
melissa_busy = [
    (9 * 60 + 30, 10 * 60),  # 9:30-10:00
    (14 * 60 + 30, 15 * 60)  # 14:30-15:00
]
melissa_free = get_free_intervals(melissa_busy, work_start, work_end)

# Frank's busy intervals
frank_busy = [
    (10 * 60, 10 * 60 + 30),  # 10:00-10:30
    (11 * 60, 11 * 60 + 30),  # 11:00-11:30
    (12 * 60 + 30, 13 * 60),  # 12:30-13:00
    (13 * 60 + 30, 14 * 60 + 30),  # 13:30-14:30
    (15 * 60, 16 * 60),  # 15:00-16:00
    (16 * 60 + 30, 17 * 60)  # 16:30-17:00
]
frank_free = get_free_intervals(frank_busy, work_start, work_end)

# Apply Frank's constraint (no meeting after 9:30 = 570 minutes)
frank_free_constrained = []
for start, end in frank_free:
    constrained_end = min(end, 9 * 60 + 30)  # 570
    if start < constrained_end:
        frank_free_constrained.append((start, constrained_end))

# Find common intervals between all three
common_intervals = []
for e in emily_free:
    for m in melissa_free:
        overlap_start = max(e[0], m[0])
        overlap_end = min(e[1], m[1])
        if overlap_end - overlap_start >= 30:  # At least 30 minutes
            for f in frank_free_constrained:
                final_start = max(overlap_start, f[0])
                final_end = min(overlap_end, f[1])
                if final_end - final_start >= 30:
                    common_intervals.append((final_start, final_end))

# Output the first valid interval
if common_intervals:
    start, end = common_intervals[0]
    start_time = minutes_to_time(start)
    end_time = minutes_to_time(end)
    print(f"{start_time}:{end_time} Monday")
else:
    print("No suitable time found")