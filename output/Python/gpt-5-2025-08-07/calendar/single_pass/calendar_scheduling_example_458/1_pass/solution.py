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

def invert_within(busy: List[Tuple[int, int]], window: Tuple[int, int]) -> List[Tuple[int, int]]:
    ws, we = window
    busy = [(max(ws, s), min(we, e)) for s, e in busy if e > ws and s < we]
    busy = merge_intervals(busy)
    free = []
    cur = ws
    for s, e in busy:
        if s > cur:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < we:
        free.append((cur, we))
    return free

def intersect(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    i, j = 0, 0
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
work_window = (to_minutes("09:00"), to_minutes("17:00"))
duration = 30  # minutes
preference_after = to_minutes("14:00")  # Wayne's preference

participants_busy = {
    "Wayne": [],
    "Melissa": [("10:00","11:00"), ("12:30","14:00"), ("15:00","15:30")],
    "Catherine": [],
    "Gregory": [("12:30","13:00"), ("15:30","16:00")],
    "Victoria": [("09:00","09:30"), ("10:30","11:30"), ("13:00","14:00"), ("14:30","15:00"), ("15:30","16:30")],
    "Thomas": [("10:00","12:00"), ("12:30","13:00"), ("14:30","16:00")],
    "Jennifer": [("09:00","09:30"), ("10:00","10:30"), ("11:00","13:00"), ("13:30","14:30"), ("15:00","15:30"), ("16:00","16:30")],
}

# Convert to minutes
participants_busy_min = {
    person: [(to_minutes(s), to_minutes(e)) for s, e in intervals]
    for person, intervals in participants_busy.items()
}

# Compute free intervals for each participant within work hours
participants_free = {
    person: invert_within(busy, work_window)
    for person, busy in participants_busy_min.items()
}

# Intersect all free intervals
common_free = None
for free in participants_free.values():
    if common_free is None:
        common_free = free
    else:
        common_free = intersect(common_free, free)

# Find a slot honoring preference; otherwise fallback to any
meeting_start = meeting_end = None

# Try honoring preference (start at or after preference_after)
for s, e in common_free:
    start = max(s, preference_after)
    if e - start >= duration:
        meeting_start, meeting_end = start, start + duration
        break

# Fallback if needed
if meeting_start is None:
    for s, e in common_free:
        if e - s >= duration:
            meeting_start, meeting_end = s, s + duration
            break

# Output
print(f"{to_hhmm(meeting_start)}:{to_hhmm(meeting_end)}")
print(day)