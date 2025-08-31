def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"


def get_free_intervals(work_start, work_end, busy_intervals, extra_end=None):
    busy_intervals.sort()
    free = []
    prev_end = work_start
    for start, end in busy_intervals:
        if start > prev_end:
            free.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free.append((prev_end, work_end))
    if extra_end is not None:
        adjusted = []
        for s, e in free:
            new_e = min(e, extra_end)
            if s < new_e:
                adjusted.append((s, new_e))
        free = adjusted
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


# Define work hours
work_start = 9 * 60   # 540
work_end = 17 * 60    # 1020

# Anthony's busy times
anthony_busy = [
    (9*60 + 30, 10*60),       # 9:30-10:00
    (12*60, 13*60),           # 12:00-13:00
    (16*60, 16*60 + 30)       # 16:00-16:30
]

# Pamela's busy times
pamela_busy = [
    (9*60 + 30, 10*60),       # 9:30-10:00
    (16*60 + 30, 17*60)       # 16:30-17:00
]
pamela_extra_end = 14 * 60 + 30  # 14:30

# Zachary's busy times
zachary_busy = [
    (9*60, 11*60 + 30),       # 9:00-11:30
    (12*60, 12*60 + 30),      # 12:00-12:30
    (13*60, 13*60 + 30),      # 13:00-13:30
    (14*60 + 30, 15*60),      # 14:30-15:00
    (16*60, 17*60)            # 16:00-17:00
]

# Generate free intervals
anthony_free = get_free_intervals(work_start, work_end, anthony_busy)
pamela_free = get_free_intervals(work_start, work_end, pamela_busy, extra_end=pamela_extra_end)
zachary_free = get_free_intervals(work_start, work_end, zachary_busy)

# Find common intervals
common_1 = interval_intersection(anthony_free, pamela_free)
common_2 = interval_intersection(common_1, zachary_free)

# Find the first suitable interval
for start, end in common_2:
    if end - start >= 60:
        start_time = minutes_to_time(start)
        end_time = minutes_to_time(start + 60)
        day = "Monday"
        print(f"{start_time}:{end_time} {day}")
        break
