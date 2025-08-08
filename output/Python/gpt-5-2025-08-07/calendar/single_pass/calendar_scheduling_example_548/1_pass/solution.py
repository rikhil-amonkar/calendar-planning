from typing import List, Tuple

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_str(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

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

def subtract_busy_from_window(window: Tuple[int, int], busy: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    ws, we = window
    busy = merge_intervals([(max(ws, s), min(we, e)) for s, e in busy if e > ws and s < we])
    free = []
    cursor = ws
    for s, e in busy:
        if cursor < s:
            free.append((cursor, s))
        cursor = max(cursor, e)
    if cursor < we:
        free.append((cursor, we))
    return free

def intersect(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    i = j = 0
    res = []
    a = sorted(a)
    b = sorted(b)
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

# Problem setup (Monday, 09:00-17:00, 30 minutes)
day = "Monday"
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
work_window = (work_start, work_end)
meeting_duration = 30

# Participants' schedules
# Judy is free the entire day within work hours
judy_free = [work_window]

# Nicole busy times and preference (would rather not meet before 16:00)
nicole_busy = [
    (to_minutes("09:00"), to_minutes("10:00")),
    (to_minutes("10:30"), to_minutes("16:30")),
]
nicole_prefer_after = to_minutes("16:00")

nicole_free = subtract_busy_from_window(work_window, nicole_busy)

# Common availability
common = judy_free
common = intersect(common, nicole_free)

# Helper to find a slot honoring a preferred earliest start if possible
def find_slot(intervals: List[Tuple[int, int]], duration: int, prefer_after: int = None) -> Tuple[int, int]:
    if prefer_after is not None:
        for s, e in intervals:
            start = max(s, prefer_after)
            if start + duration <= e:
                return start, start + duration
    for s, e in intervals:
        if s + duration <= e:
            return s, s + duration
    return None

slot = find_slot(common, meeting_duration, prefer_after=nicole_prefer_after)

# Output
if slot:
    start, end = slot
    print(f"{{{to_str(start)}:{to_str(end)}}}")
    print(day)
else:
    # Fallback (should not happen per problem statement)
    print("{No available slot}")
    print(day)