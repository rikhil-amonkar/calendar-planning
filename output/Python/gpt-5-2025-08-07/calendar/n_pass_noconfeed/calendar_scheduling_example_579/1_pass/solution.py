from typing import List, Tuple

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

def invert_busy_to_free(busy: List[Tuple[int, int]], window: Tuple[int, int]) -> List[Tuple[int, int]]:
    start, end = window
    # Normalize and cap busy intervals to the window
    clipped = []
    for s, e in busy:
        s = max(s, start)
        e = min(e, end)
        if s < e:
            clipped.append((s, e))
    # Add window bounds as sentinels
    points = [(start, start)] + sorted(clipped) + [(end, end)]
    free = []
    # Build free intervals between busy ones
    current = start
    for s, e in points[1:]:
        if current < s:
            free.append((current, s))
        current = max(current, e)
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

def first_slot(intervals: List[Tuple[int, int]], duration: int) -> Tuple[int, int]:
    for s, e in intervals:
        if e - s >= duration:
            return (s, s + duration)
    raise ValueError("No suitable slot found")

# Problem setup
day = "Monday"
meeting_duration_min = 30
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")

# Participants' busy schedules
christine_busy = [
    (to_minutes("11:00"), to_minutes("11:30")),
    (to_minutes("15:00"), to_minutes("15:30")),
]
helen_busy = [
    (to_minutes("09:30"), to_minutes("10:30")),
    (to_minutes("11:00"), to_minutes("11:30")),
    (to_minutes("12:00"), to_minutes("12:30")),
    (to_minutes("13:30"), to_minutes("16:00")),
    (to_minutes("16:30"), to_minutes("17:00")),
]

# Additional constraint: Helen cannot meet after 15:00 on Monday
helen_end_cap = to_minutes("15:00")

# Compute free intervals
christine_free = invert_busy_to_free(christine_busy, (work_start, work_end))
helen_free = invert_busy_to_free(helen_busy, (work_start, helen_end_cap))

# Intersect all participants' free intervals
common_free = intersect_intervals(christine_free, helen_free)

# Pick the first slot that fits the duration
slot_start, slot_end = first_slot(common_free, meeting_duration_min)

# Output
print(day)
print(f"{{{to_hhmm(slot_start)}:{to_hhmm(slot_end)}}}")