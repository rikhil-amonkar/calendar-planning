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
        ls, le = merged[-1]
        if s <= le:
            merged[-1] = (ls, max(le, e))
        else:
            merged.append((s, e))
    return merged

def invert_intervals(busy: List[Tuple[int, int]], window: Tuple[int, int]) -> List[Tuple[int, int]]:
    start, end = window
    if not busy:
        return [(start, end)]
    busy = merge_intervals([(max(start, s), min(end, e)) for s, e in busy if e > start and s < end])
    free = []
    cur = start
    for s, e in busy:
        if cur < s:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < end:
        free.append((cur, end))
    return free

def intersect(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    i = j = 0
    result = []
    while i < len(a) and j < len(b):
        s = max(a[i][0], b[j][0])
        e = min(a[i][1], b[j][1])
        if s < e:
            result.append((s, e))
        if a[i][1] < b[j][1]:
            i += 1
        else:
            j += 1
    return result

# Problem setup
day = "Monday"
work_window = (to_minutes("09:00"), to_minutes("17:00"))
duration = 60  # minutes

participants_busy = {
    "Evelyn": [],
    "Joshua": [(to_minutes("11:00"), to_minutes("12:30")),
               (to_minutes("13:30"), to_minutes("14:30")),
               (to_minutes("16:30"), to_minutes("17:00"))],
    "Kevin": [],
    "Gerald": [],
    "Jerry": [(to_minutes("09:00"), to_minutes("09:30")),
              (to_minutes("10:30"), to_minutes("12:00")),
              (to_minutes("12:30"), to_minutes("13:00")),
              (to_minutes("13:30"), to_minutes("14:00")),
              (to_minutes("14:30"), to_minutes("15:00")),
              (to_minutes("15:30"), to_minutes("16:00"))],
    "Jesse": [(to_minutes("09:00"), to_minutes("09:30")),
              (to_minutes("10:30"), to_minutes("12:00")),
              (to_minutes("12:30"), to_minutes("13:00")),
              (to_minutes("14:30"), to_minutes("15:00")),
              (to_minutes("15:30"), to_minutes("16:30"))],
    "Kenneth": [(to_minutes("10:30"), to_minutes("12:30")),
                (to_minutes("13:30"), to_minutes("14:00")),
                (to_minutes("14:30"), to_minutes("15:00")),
                (to_minutes("15:30"), to_minutes("16:00")),
                (to_minutes("16:30"), to_minutes("17:00"))],
}

# Compute common free intervals
common_free = [work_window]
for name, busy in participants_busy.items():
    free = invert_intervals(busy, work_window)
    common_free = intersect(common_free, free)
    if not common_free:
        break

# Find earliest slot that fits the duration
start_time, end_time = None, None
for s, e in common_free:
    if e - s >= duration:
        start_time = s
        end_time = s + duration
        break

if start_time is None:
    raise RuntimeError("No suitable time found, but the problem statement guarantees one exists.")

time_range_str = f"{to_hhmm(start_time)}:{to_hhmm(end_time)}"
print(f"{{{time_range_str}}}")
print(day)