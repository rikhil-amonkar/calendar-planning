from typing import List, Tuple

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

def merge_intervals(intervals: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    if not intervals:
        return []
    intervals.sort()
    merged = [intervals[0]]
    for s, e in intervals[1:]:
        last_s, last_e = merged[-1]
        if s <= last_e:  # overlap or touching
            merged[-1] = (last_s, max(last_e, e))
        else:
            merged.append((s, e))
    return merged

def invert_busy_to_free(busy: List[Tuple[int, int]], work_start: int, work_end: int) -> List[Tuple[int, int]]:
    busy = merge_intervals([b for b in busy if b[1] > work_start and b[0] < work_end])
    free = []
    prev = work_start
    for s, e in busy:
        s = max(s, work_start)
        e = min(e, work_end)
        if s > prev:
            free.append((prev, s))
        prev = max(prev, e)
    if prev < work_end:
        free.append((prev, work_end))
    return free

def intersect_intervals(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
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

def earliest_slot(common_free: List[Tuple[int, int]], duration: int, prefer_end_before: int = None) -> Tuple[int, int]:
    candidates = []
    for s, e in common_free:
        if e - s >= duration:
            candidates.append((s, s + duration))
    if prefer_end_before is not None:
        preferred = [c for c in candidates if c[1] <= prefer_end_before]
        if preferred:
            return min(preferred, key=lambda x: x[0])
    return min(candidates, key=lambda x: x[0])

# Input data (example task)
day = "Monday"
work_start, work_end = to_minutes("09:00"), to_minutes("17:00")
duration = 30  # minutes

schedules = {
    "Lisa":   [("09:00","10:00"), ("10:30","11:30"), ("12:30","13:00"), ("16:00","16:30")],
    "Bobby":  [("09:00","09:30"), ("10:00","10:30"), ("11:30","12:00"), ("15:00","15:30")],
    "Randy":  [("09:30","10:00"), ("10:30","11:00"), ("11:30","12:30"), ("13:00","13:30"), ("14:30","15:30"), ("16:00","16:30")],
}

# Convert schedules to minutes
busy_minutes = {
    name: [(to_minutes(s), to_minutes(e)) for s, e in slots]
    for name, slots in schedules.items()
}

# Compute free intervals for each participant
free_intervals = {
    name: invert_busy_to_free(busy, work_start, work_end)
    for name, busy in busy_minutes.items()
}

# Find common free time across all participants
participants = list(free_intervals.keys())
common = free_intervals[participants[0]]
for p in participants[1:]:
    common = intersect_intervals(common, free_intervals[p])

# Preference: Bobby prefers to avoid after 15:00
prefer_end_before = to_minutes("15:00")

start, end = earliest_slot(common, duration, prefer_end_before=prefer_end_before)

print(f"{{{to_hhmm(start)}:{to_hhmm(end)}}} {day}")