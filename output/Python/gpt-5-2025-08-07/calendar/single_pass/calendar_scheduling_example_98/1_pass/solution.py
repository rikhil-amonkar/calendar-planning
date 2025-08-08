from typing import List, Tuple

# Helper functions
def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_time_str(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

def merge_intervals(intervals: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    if not intervals:
        return []
    intervals.sort()
    merged = [intervals[0]]
    for s, e in intervals[1:]:
        last_s, last_e = merged[-1]
        if s <= last_e:
            merged[-1] = (last_s, max(last_e, e))
        else:
            merged.append((s, e))
    return merged

def invert_intervals(busy: List[Tuple[int, int]], window: Tuple[int, int]) -> List[Tuple[int, int]]:
    start, end = window
    if not busy:
        return [(start, end)]
    busy = merge_intervals(busy)
    free = []
    cur = start
    for s, e in busy:
        if s > cur:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < end:
        free.append((cur, end))
    return free

def intersect_two(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    i = j = 0
    out = []
    while i < len(a) and j < len(b):
        s = max(a[i][0], b[j][0])
        e = min(a[i][1], b[j][1])
        if s < e:
            out.append((s, e))
        if a[i][1] < b[j][1]:
            i += 1
        else:
            j += 1
    return out

def find_slot(free_sets: List[List[Tuple[int, int]]], duration: int) -> Tuple[int, int]:
    from functools import reduce
    common = reduce(intersect_two, free_sets)
    for s, e in common:
        if e - s >= duration:
            return (s, s + duration)
    raise ValueError("No suitable slot found")

# Problem data
day = "Monday"
work_start, work_end = to_minutes("09:00"), to_minutes("17:00")
duration = 30  # minutes

# Busy schedules
juan_busy = [
    (to_minutes("09:00"), to_minutes("10:30")),
    (to_minutes("15:30"), to_minutes("16:00")),
]
marilyn_busy = [
    (to_minutes("11:00"), to_minutes("11:30")),
    (to_minutes("12:30"), to_minutes("13:00")),
]
ronald_busy = [
    (to_minutes("09:00"), to_minutes("10:30")),
    (to_minutes("12:00"), to_minutes("12:30")),
    (to_minutes("13:00"), to_minutes("13:30")),
    (to_minutes("14:00"), to_minutes("16:30")),
]

# Constraint: Juan cannot meet after 16:00 (meeting must end by 16:00)
juan_latest_end = to_minutes("16:00")

# Compute free intervals within work hours
work_window = (work_start, work_end)
juan_window = (work_start, min(work_end, juan_latest_end))  # enforce Juan's constraint
juan_free = invert_intervals(juan_busy, juan_window)
marilyn_free = invert_intervals(marilyn_busy, work_window)
ronald_free = invert_intervals(ronald_busy, work_window)

# Find earliest feasible slot
start_min, end_min = find_slot([juan_free, marilyn_free, ronald_free], duration)

# Output in required formats
time_range_str = f"{{{to_time_str(start_min)}:{to_time_str(end_min)}}}"
print(time_range_str)
print(day)