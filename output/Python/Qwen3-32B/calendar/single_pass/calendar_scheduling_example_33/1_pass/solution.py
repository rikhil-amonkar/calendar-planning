def generate_free_intervals(work_start, work_end, busy_intervals):
    if not busy_intervals:
        return [(work_start, work_end)]
    # Sort by start time
    busy = sorted(busy_intervals, key=lambda x: x[0])
    # Merge overlapping intervals
    merged = []
    current_start, current_end = busy[0]
    for start, end in busy[1:]:
        if start <= current_end:
            current_end = max(current_end, end)
        else:
            merged.append((current_start, current_end))
            current_start, current_end = start, end
    merged.append((current_start, current_end))
    # Subtract merged busy intervals from work day
    free = []
    prev_end = work_start
    for start, end in merged:
        if prev_end < start:
            free.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free.append((prev_end, work_end))
    return free

def interval_intersection(a, b):
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

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

work_start = 9 * 60
work_end = 17 * 60

# Lisa's busy times
lisa_busy = [
    (540, 600),
    (630, 690),
    (750, 780),
    (960, 990)
]
lisa_free = generate_free_intervals(work_start, work_end, lisa_busy)

# Bobby's busy times
bobby_busy = [
    (540, 570),
    (600, 630),
    (690, 720),
    (900, 930)
]
bobby_free = generate_free_intervals(work_start, work_end, bobby_busy)

# Randy's busy times
randy_busy = [
    (570, 600),
    (630, 660),
    (690, 750),
    (780, 810),
    (870, 930),
    (960, 990)
]
randy_free = generate_free_intervals(work_start, work_end, randy_busy)

# Compute intersections
lisa_bobby_free = interval_intersection(lisa_free, bobby_free)
common_free = interval_intersection(lisa_bobby_free, randy_free)

# Apply constraints: duration >= 30 and end <= 900 (15:00)
valid_slots = []
for start, end in common_free:
    if end - start >= 30 and end <= 900:
        valid_slots.append((start, start + 30))

# Find the earliest valid slot
earliest = min(valid_slots, key=lambda x: x[0])
start_time = earliest[0]
end_time = earliest[1]
day = "Monday"

start_str = minutes_to_time(start_time)
end_str = minutes_to_time(end_time)

print(f"{start_str}:{end_str} {day}")