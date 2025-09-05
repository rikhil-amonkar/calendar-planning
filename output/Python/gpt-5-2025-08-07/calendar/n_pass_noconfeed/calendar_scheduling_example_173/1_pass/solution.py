from typing import List, Tuple

# Helper functions
def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_time_str(minutes: int) -> str:
    return f"{minutes//60:02d}:{minutes%60:02d}"

def invert_busy_to_free(busy: List[Tuple[int, int]], day_window: Tuple[int, int]) -> List[Tuple[int, int]]:
    start, end = day_window
    busy = sorted(busy)
    free = []
    cur = start
    for b_start, b_end in busy:
        if b_end <= cur:
            continue
        if b_start > cur:
            free.append((cur, min(b_start, end)))
        cur = max(cur, b_end)
        if cur >= end:
            break
    if cur < end:
        free.append((cur, end))
    # Filter out any zero or negative intervals
    return [(s, e) for s, e in free if e - s > 0]

def intersect_intervals(a: List[Tuple[int,int]], b: List[Tuple[int,int]]) -> List[Tuple[int,int]]:
    i = j = 0
    res = []
    while i < len(a) and j < len(b):
        s = max(a[i][0], b[j][0])
        e = min(a[i][1], b[j][1])
        if s < e:
            res.append((s, e))
        if a[i][1] < b[j][1]:
            i += 1
        else:
            j += 1
    return res

def filter_by_duration(slots: List[Tuple[int,int]], duration: int) -> List[Tuple[int,int]]:
    return [(s, e) for s, e in slots if e - s >= duration]

# Data setup for the task
day = "Monday"
work_start, work_end = to_minutes("09:00"), to_minutes("17:00")
meeting_duration = 30  # minutes

schedules = {
    "Jacqueline": [("09:00","09:30"), ("11:00","11:30"), ("12:30","13:00"), ("15:30","16:00")],
    "Harold":     [("10:00","10:30"), ("13:00","13:30"), ("15:00","17:00")],
    "Arthur":     [("09:00","09:30"), ("10:00","12:30"), ("14:30","15:00"), ("15:30","17:00")],
    "Kelly":      [("09:00","09:30"), ("10:00","11:00"), ("11:30","12:30"), ("14:00","15:00"), ("15:30","16:00")],
}

# Convert busy schedules to minutes
busy_minutes = {
    name: [(to_minutes(s), to_minutes(e)) for s, e in slots]
    for name, slots in schedules.items()
}

# Apply Harold's constraint: not after 13:00 on Monday (meeting must end by 13:00)
constraint_end = to_minutes("13:00")
search_window = (work_start, min(work_end, constraint_end))

# Compute free intervals for each participant within the constrained search window
free_intervals = []
for name, busy in busy_minutes.items():
    # Trim busy intervals to the search window
    trimmed = []
    for s, e in busy:
        if e <= search_window[0] or s >= search_window[1]:
            continue
        trimmed.append((max(s, search_window[0]), min(e, search_window[1])))
    free = invert_busy_to_free(trimmed, search_window)
    free_intervals.append(free)

# Intersect all participants' free intervals
common = free_intervals[0]
for fi in free_intervals[1:]:
    common = intersect_intervals(common, fi)
    if not common:
        break

# Filter by meeting duration
candidates = filter_by_duration(common, meeting_duration)

# Choose the earliest feasible slot
start_min, end_min = candidates[0][0], candidates[0][0] + meeting_duration

# Output in required formats
time_range_str = f"{to_time_str(start_min)}:{to_time_str(end_min)}"
print(f"{{{time_range_str}}}")
print(day)