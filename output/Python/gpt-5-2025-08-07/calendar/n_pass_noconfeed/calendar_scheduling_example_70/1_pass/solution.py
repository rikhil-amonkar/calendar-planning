from typing import List, Tuple

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
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

def invert_intervals(busy: List[Tuple[int, int]], start: int, end: int) -> List[Tuple[int, int]]:
    busy = [(max(start, s), min(end, e)) for s, e in busy if e > start and s < end]
    busy = merge_intervals(busy)
    free = []
    prev = start
    for s, e in busy:
        if s > prev:
            free.append((prev, s))
        prev = max(prev, e)
    if prev < end:
        free.append((prev, end))
    return free

def intersect(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
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

# Inputs for the task
day = "Monday"
work_start, work_end = to_minutes("09:00"), to_minutes("17:00")
duration = 30  # minutes

busy_denise = [(to_minutes("12:00"), to_minutes("12:30")),
               (to_minutes("15:30"), to_minutes("16:00"))]

busy_angela = []  # no meetings

busy_natalie = [(to_minutes("09:00"), to_minutes("11:30")),
                (to_minutes("12:00"), to_minutes("13:00")),
                (to_minutes("14:00"), to_minutes("14:30")),
                (to_minutes("15:00"), to_minutes("17:00"))]

# Compute free intervals within work hours
free_denise = invert_intervals(busy_denise, work_start, work_end)
free_angela = invert_intervals(busy_angela, work_start, work_end)
free_natalie = invert_intervals(busy_natalie, work_start, work_end)

# Find common free slots
common_free = intersect(intersect(free_denise, free_angela), free_natalie)

# Pick earliest slot that fits duration
start_time = end_time = None
for s, e in common_free:
    if e - s >= duration:
        start_time = s
        end_time = s + duration
        break

if start_time is None:
    raise RuntimeError("No suitable meeting time found, but a solution was expected.")

output = f"{day} {{{to_hhmm(start_time)}:{to_hhmm(end_time)}}}"
print(output)