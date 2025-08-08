from typing import List, Tuple

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m//60:02d}:{m%60:02d}"

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

def invert_intervals(busy: List[Tuple[int, int]], start: int, end: int) -> List[Tuple[int, int]]:
    busy = merge_intervals([(max(start, s), min(end, e)) for s, e in busy if e > start and s < end])
    free = []
    cursor = start
    for s, e in busy:
        if cursor < s:
            free.append((cursor, s))
        cursor = max(cursor, e)
    if cursor < end:
        free.append((cursor, end))
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

def intersect_all(interval_sets: List[List[Tuple[int, int]]]) -> List[Tuple[int, int]]:
    if not interval_sets:
        return []
    res = interval_sets[0]
    for nxt in interval_sets[1:]:
        res = intersect_two(res, nxt)
        if not res:
            break
    return res

# Setup
day = "Monday"
work_start, work_end = to_minutes("09:00"), to_minutes("17:00")
meeting_duration = 30  # minutes

# Busy schedules
emily_busy = [
    (to_minutes("10:00"), to_minutes("10:30")),
    (to_minutes("11:30"), to_minutes("12:30")),
    (to_minutes("14:00"), to_minutes("15:00")),
    (to_minutes("16:00"), to_minutes("16:30")),
]

melissa_busy = [
    (to_minutes("09:30"), to_minutes("10:00")),
    (to_minutes("14:30"), to_minutes("15:00")),
]

frank_busy = [
    (to_minutes("10:00"), to_minutes("10:30")),
    (to_minutes("11:00"), to_minutes("11:30")),
    (to_minutes("12:30"), to_minutes("13:00")),
    (to_minutes("13:30"), to_minutes("14:30")),
    (to_minutes("15:00"), to_minutes("16:00")),
    (to_minutes("16:30"), to_minutes("17:00")),
]
# Preference: Frank does not want to meet after 09:30 -> block [09:30, work_end]
frank_busy.append((to_minutes("09:30"), work_end))

# Compute free intervals within work hours
emily_free = invert_intervals(emily_busy, work_start, work_end)
melissa_free = invert_intervals(melissa_busy, work_start, work_end)
frank_free = invert_intervals(frank_busy, work_start, work_end)

# Find common availability
common = intersect_all([emily_free, melissa_free, frank_free])

# Pick the earliest slot that fits the duration
proposed = None
for s, e in common:
    if e - s >= meeting_duration:
        proposed = (s, s + meeting_duration)
        break

if not proposed:
    raise RuntimeError("No suitable meeting time found, though one was expected.")

start_str, end_str = to_hhmm(proposed[0]), to_hhmm(proposed[1])
print(f"{day} {{{start_str}:{end_str}}}")