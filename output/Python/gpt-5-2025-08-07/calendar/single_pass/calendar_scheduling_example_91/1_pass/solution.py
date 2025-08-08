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
        if s <= last_e:
            merged[-1] = (last_s, max(last_e, e))
        else:
            merged.append((s, e))
    return merged

def complement_within(work_start: int, work_end: int, busy: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    free = []
    cur = work_start
    for s, e in busy:
        s = max(s, work_start)
        e = min(e, work_end)
        if s > cur:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < work_end:
        free.append((cur, work_end))
    return free

def intersect_intervals(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
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

# Inputs
day = "Monday"
work_start, work_end = to_minutes("09:00"), to_minutes("17:00")
duration = 60  # minutes

schedules = {
    "Danielle": [("09:00","10:00"), ("10:30","11:00"), ("14:30","15:00"), ("15:30","16:00"), ("16:30","17:00")],
    "Bruce":    [("11:00","11:30"), ("12:30","13:00"), ("14:00","14:30"), ("15:30","16:00")],
    "Eric":     [("09:00","09:30"), ("10:00","11:00"), ("11:30","13:00"), ("14:30","15:30")],
}

# Prepare free intervals for each participant
free_by_person = []
for person, meetings in schedules.items():
    busy = [(to_minutes(s), to_minutes(e)) for s, e in meetings]
    busy = [(max(work_start, s), min(work_end, e)) for s, e in busy if min(work_end, e) > max(work_start, s)]
    busy = merge_intervals(busy)
    free = complement_within(work_start, work_end, busy)
    free_by_person.append(free)

# Intersect all free intervals
common_free = free_by_person[0]
for free in free_by_person[1:]:
    common_free = intersect_intervals(common_free, free)

# Find earliest slot of required duration
start_time = end_time = None
for s, e in common_free:
    if e - s >= duration:
        start_time = s
        end_time = s + duration
        break

if start_time is None:
    raise RuntimeError("No common slot found, but a solution was expected.")

print(f"{{{to_hhmm(start_time)}:{to_hhmm(end_time)}}}")
print(day)