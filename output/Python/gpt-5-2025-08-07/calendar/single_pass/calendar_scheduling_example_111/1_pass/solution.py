from typing import List, Tuple

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
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

def invert_within(bounds: Tuple[int, int], busy: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    start, end = bounds
    if not busy:
        return [(start, end)]
    free = []
    cur = start
    for s, e in busy:
        s = max(s, start)
        e = min(e, end)
        if e <= start or s >= end:
            continue
        if s > cur:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < end:
        free.append((cur, end))
    return free

def intersect_lists(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
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

# Parameters
day = "Monday"
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
meeting_duration = 30  # minutes

# Busy schedules (inclusive of day constraints)
gregory_busy = [("09:00","10:00"), ("10:30","11:30"), ("12:30","13:00"), ("13:30","14:00")]
natalie_busy = []  # wide open
christine_busy = [("09:00","11:30"), ("13:30","17:00")]
vincent_busy = [("09:00","09:30"), ("10:30","12:00"), ("12:30","14:00"), ("14:30","17:00")]

def prepare_busy(busy_str: List[Tuple[str, str]]) -> List[Tuple[int, int]]:
    return merge_intervals([(to_minutes(s), to_minutes(e)) for s, e in busy_str])

bounds = (work_start, work_end)
gregory_free = invert_within(bounds, prepare_busy(gregory_busy))
natalie_free = invert_within(bounds, prepare_busy(natalie_busy))
christine_free = invert_within(bounds, prepare_busy(christine_busy))
vincent_free = invert_within(bounds, prepare_busy(vincent_busy))

# Find common free slots
common = gregory_free
for lst in (natalie_free, christine_free, vincent_free):
    common = intersect_lists(common, lst)

# Pick earliest slot meeting the duration
proposed = None
for s, e in common:
    if e - s >= meeting_duration:
        proposed = (s, s + meeting_duration)
        break

if proposed is None:
    raise RuntimeError("No suitable time found, but a solution was expected.")

start_str = to_hhmm(proposed[0])
end_str = to_hhmm(proposed[1])

print(day)
print(f"{{{start_str}:{end_str}}}")