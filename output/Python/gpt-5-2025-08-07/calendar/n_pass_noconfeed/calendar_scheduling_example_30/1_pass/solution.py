from typing import List, Tuple

# Utility functions
def to_minutes(hhmm: str) -> int:
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def to_hhmm(minutes: int) -> str:
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

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

def clip_interval(interval: Tuple[int, int], bounds: Tuple[int, int]) -> Tuple[int, int] | None:
    s, e = interval
    bs, be = bounds
    s2, e2 = max(s, bs), min(e, be)
    return (s2, e2) if s2 < e2 else None

def complement_within(bounds: Tuple[int, int], busy: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    bs, be = bounds
    # Clip busy to bounds and merge
    clipped = []
    for iv in busy:
        c = clip_interval(iv, bounds)
        if c:
            clipped.append(c)
    busy_merged = merge_intervals(clipped)
    free = []
    cursor = bs
    for s, e in busy_merged:
        if cursor < s:
            free.append((cursor, s))
        cursor = max(cursor, e)
    if cursor < be:
        free.append((cursor, be))
    return free

def intersect_intervals(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    i = j = 0
    out = []
    while i < len(a) and j < len(b):
        s = max(a[i][0], b[j][0])
        e = min(a[i][1], b[j][1])
        if s < e:
            out.append((s, e))
        # advance pointer with smaller end
        if a[i][1] <= b[j][1]:
            i += 1
        else:
            j += 1
    return out

def slice_intervals(intervals: List[Tuple[int, int]], bounds: Tuple[int, int]) -> List[Tuple[int, int]]:
    sliced = []
    for iv in intervals:
        c = clip_interval(iv, bounds)
        if c:
            sliced.append(c)
    return sliced

def find_slot(common_free: List[Tuple[int, int]], duration: int) -> Tuple[int, int] | None:
    for s, e in common_free:
        if e - s >= duration:
            return (s, s + duration)
    return None

# Problem setup (Monday)
day = "Monday"
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
work_bounds = (work_start, work_end)
duration = 30  # minutes

# Existing busy schedules
jeffrey_busy = [
    (to_minutes("09:30"), to_minutes("10:00")),
    (to_minutes("10:30"), to_minutes("11:00")),
]
virginia_busy = [
    (to_minutes("09:00"), to_minutes("09:30")),
    (to_minutes("10:00"), to_minutes("10:30")),
    (to_minutes("14:30"), to_minutes("15:00")),
    (to_minutes("16:00"), to_minutes("16:30")),
]
melissa_busy = [
    (to_minutes("09:00"), to_minutes("11:30")),
    (to_minutes("12:00"), to_minutes("12:30")),
    (to_minutes("13:00"), to_minutes("15:00")),
    (to_minutes("16:00"), to_minutes("17:00")),
]

# Preferences
# Melissa would rather not meet after 14:00 (prefer the meeting to end by 14:00 if possible)
preferred_latest_end = to_minutes("14:00")
preferred_bounds = (work_start, preferred_latest_end)

# Compute free intervals within work hours
jeffrey_free = complement_within(work_bounds, jeffrey_busy)
virginia_free = complement_within(work_bounds, virginia_busy)
melissa_free = complement_within(work_bounds, melissa_busy)

# Intersection of all free intervals
common_free = intersect_intervals(
    intersect_intervals(jeffrey_free, virginia_free),
    melissa_free
)

# First try to satisfy preference (meeting ends by 14:00)
preferred_common = slice_intervals(common_free, preferred_bounds)
slot = find_slot(preferred_common, duration)

# If not found, fall back to any time within work hours
if slot is None:
    slot = find_slot(common_free, duration)

# Output result
if slot:
    start_str = to_hhmm(slot[0])
    end_str = to_hhmm(slot[1])
    print(f"{day} {{{start_str}:{end_str}}}")
else:
    # Problem statement guarantees a solution exists; this is a safety fallback.
    print(f"{day} {{No available slot}}")