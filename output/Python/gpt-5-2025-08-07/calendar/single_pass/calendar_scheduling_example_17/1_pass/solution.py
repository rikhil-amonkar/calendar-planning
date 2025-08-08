from typing import List, Tuple

# Utility functions
def to_minutes(hhmm: str) -> int:
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def fmt(m: int) -> str:
    return f"{m//60:02d}:{m%60:02d}"

def merge_intervals(intervals: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    if not intervals:
        return []
    intervals = sorted(intervals)
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
    busy = merge_intervals([i for i in busy if not (i[1] <= start or i[0] >= end)])
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

def intersect_all(lists: List[List[Tuple[int, int]]]) -> List[Tuple[int, int]]:
    if not lists:
        return []
    res = lists[0]
    for lst in lists[1:]:
        res = intersect_two(res, lst)
        if not res:
            break
    return res

# Problem setup (Monday)
day = "Monday"
work_window = (to_minutes("09:00"), to_minutes("17:00"))
meeting_duration = 30  # minutes

# Busy schedules
margaret_busy = [
    (to_minutes("09:00"), to_minutes("10:00")),
    (to_minutes("10:30"), to_minutes("11:00")),
    (to_minutes("11:30"), to_minutes("12:00")),
    (to_minutes("13:00"), to_minutes("13:30")),
    (to_minutes("15:00"), to_minutes("15:30")),
]

donna_busy = [
    (to_minutes("14:30"), to_minutes("15:00")),
    (to_minutes("16:00"), to_minutes("16:30")),
]

helen_busy = [
    (to_minutes("09:00"), to_minutes("09:30")),
    (to_minutes("10:00"), to_minutes("11:30")),
    (to_minutes("13:00"), to_minutes("14:00")),
    (to_minutes("14:30"), to_minutes("15:00")),
    (to_minutes("15:30"), to_minutes("17:00")),
]

# Helen's constraint: not after 13:30 (meeting must end by 13:30)
helen_latest_end = to_minutes("13:30")
helen_constraint_window = (work_window[0], helen_latest_end)

# Compute free intervals within work hours
margaret_free = invert_intervals(margaret_busy, work_window)
donna_free = invert_intervals(donna_busy, work_window)

# Apply Helen's time preference by intersecting with [09:00, 13:30]
helen_free_work = invert_intervals(helen_busy, work_window)
helen_free = intersect_two(helen_free_work, [helen_constraint_window])

# Find common availability
common = intersect_all([margaret_free, donna_free, helen_free])

# Choose the earliest slot that fits the duration
proposed = None
for s, e in common:
    if e - s >= meeting_duration:
        proposed = (s, s + meeting_duration)
        break

# Output
if proposed:
    start_str, end_str = fmt(proposed[0]), fmt(proposed[1])
    print(f"{day} {{{start_str}:{end_str}}}")
else:
    # According to the problem statement, a solution exists, but handle gracefully anyway
    print(f"{day} {{No available slot}}")