def get_free_intervals(work_start, work_end, busy_intervals):
    busy_intervals.sort()
    free_intervals = []
    prev_end = work_start
    for start, end in busy_intervals:
        if start > prev_end:
            free_intervals.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free_intervals.append((prev_end, work_end))
    return free_intervals

def find_overlapping_slots(eric_free, henry_free):
    candidates = []
    for e_start, e_end in eric_free:
        for h_start, h_end in henry_free:
            overlap_start = max(e_start, h_start)
            overlap_end = min(e_end, h_end)
            if overlap_start < overlap_end:
                duration = overlap_end - overlap_start
                if duration >= 30:
                    candidates.append((overlap_start, overlap_end))
    return candidates

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Work hours
work_start = 9 * 60  # 540
work_end = 17 * 60   # 1020

# Eric's busy times (Monday)
eric_busy = [(12 * 60, 13 * 60), (14 * 60, 15 * 60)]
eric_free = get_free_intervals(work_start, work_end, eric_busy)

# Henry's busy times (Monday)
henry_busy = [
    (9 * 60 + 30, 10 * 60),
    (10 * 60 + 30, 11 * 60),
    (11 * 60 + 30, 12 * 60 + 30),
    (13 * 60, 13 * 60 + 30),
    (14 * 60 + 30, 15 * 60),
    (16 * 60, 17 * 60)
]
henry_free = get_free_intervals(work_start, work_end, henry_busy)

# Find overlapping candidates
candidates = find_overlapping_slots(eric_free, henry_free)

# Filter candidates that meet Henry's preference (before 10:00)
preferred_candidates = []
other_candidates = []
for start, end in candidates:
    if start < 10 * 60:
        preferred_candidates.append((start, end))
    else:
        other_candidates.append((start, end))

# Select the earliest preferred candidate or earliest overall
if preferred_candidates:
    selected = min(preferred_candidates, key=lambda x: x[0])
else:
    selected = min(other_candidates, key=lambda x: x[0])

# Output
day = "Monday"
start_time = to_time_str(selected[0])
end_time = to_time_str(selected[1])
print(f"{start_time}:{end_time} {day}")