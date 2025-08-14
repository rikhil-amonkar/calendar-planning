def get_available_intervals(work_start, work_end, busy_intervals):
    busy = sorted(busy_intervals)
    available = []
    prev_end = work_start
    for start, end in busy:
        if start > prev_end:
            available.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        available.append((prev_end, work_end))
    return available

def intersect_intervals(intervals1, intervals2):
    i = 0
    j = 0
    result = []
    while i < len(intervals1) and j < len(intervals2):
        s1, e1 = intervals1[i]
        s2, e2 = intervals2[j]
        overlap_start = max(s1, s2)
        overlap_end = min(e1, e2)
        if overlap_start < overlap_end:
            result.append((overlap_start, overlap_end))
        if e1 < e2:
            i += 1
        else:
            j += 1
    return result

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

work_start = 9 * 60
work_end = 13 * 60  # 780 minutes (13:00)

# Busy intervals for each person during the 9:00-13:00 window
busy_jacqueline = [(540, 570), (660, 690), (750, 780)]
busy_harold = [(600, 630)]
busy_arthur = [(540, 570), (600, 750)]
busy_kelly = [(540, 570), (600, 660), (690, 750)]

# Compute available intervals
available_jacqueline = get_available_intervals(work_start, work_end, busy_jacqueline)
available_harold = get_available_intervals(work_start, work_end, busy_harold)
available_arthur = get_available_intervals(work_start, work_end, busy_arthur)
available_kelly = get_available_intervals(work_start, work_end, busy_kelly)

# Compute intersection
current = available_jacqueline
current = intersect_intervals(current, available_harold)
current = intersect_intervals(current, available_arthur)
current = intersect_intervals(current, available_kelly)

# Find the first suitable interval
meeting_start = None
meeting_end = None
for start, end in current:
    if end - start >= 30:
        meeting_start = start
        meeting_end = start + 30
        break

# Output
day = "Monday"
time_range = f"{to_time_str(meeting_start)}:{to_time_str(meeting_end)}"
print(f"{time_range} {day}")