from typing import List, Tuple

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

def complement_intervals(busy: List[Tuple[int, int]], day_start: int, day_end: int) -> List[Tuple[int, int]]:
    # Normalize and clip busy intervals within [day_start, day_end)
    clipped = []
    for s, e in busy:
        s = max(s, day_start)
        e = min(e, day_end)
        if s < e:
            clipped.append((s, e))
    clipped.sort()
    # Merge overlapping busy intervals
    merged = []
    for s, e in clipped:
        if not merged or s > merged[-1][1]:
            merged.append((s, e))
        else:
            merged[-1] = (merged[-1][0], max(merged[-1][1], e))
    # Build free intervals as complement
    free = []
    cur = day_start
    for s, e in merged:
        if cur < s:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < day_end:
        free.append((cur, day_end))
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

def intersect_all(interval_lists: List[List[Tuple[int, int]]]) -> List[Tuple[int, int]]:
    if not interval_lists:
        return []
    result = interval_lists[0]
    for lst in interval_lists[1:]:
        result = intersect_two(result, lst)
        if not result:
            break
    return result

def find_slot(intervals: List[Tuple[int, int]], duration: int) -> Tuple[int, int]:
    for s, e in intervals:
        if e - s >= duration:
            return s, s + duration
    return None

# Problem setup for the given task
day = "Monday"
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
meeting_duration = 60  # minutes

james_busy = [
    (to_minutes("11:30"), to_minutes("12:00")),
    (to_minutes("14:30"), to_minutes("15:00")),
]
john_busy = [
    (to_minutes("09:30"), to_minutes("11:00")),
    (to_minutes("11:30"), to_minutes("12:00")),
    (to_minutes("12:30"), to_minutes("13:30")),
    (to_minutes("14:30"), to_minutes("16:30")),
]

# Compute free intervals within work hours
james_free = complement_intervals(james_busy, work_start, work_end)
john_free = complement_intervals(john_busy, work_start, work_end)

# Find common free intervals
common_free = intersect_all([james_free, john_free])

# Select the first interval that fits the meeting duration
slot = find_slot(common_free, meeting_duration)

if slot:
    start_str = to_hhmm(slot[0])
    end_str = to_hhmm(slot[1])
    print(f"{start_str}:{end_str}")
    print(day)
else:
    # Fallback (should not happen per problem statement)
    print("No available slot")
    print(day)