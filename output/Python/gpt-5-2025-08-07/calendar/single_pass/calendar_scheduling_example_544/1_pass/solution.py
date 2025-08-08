from typing import List, Tuple

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

def invert_busy_to_free(busy: List[Tuple[int, int]], day_start: int, day_end: int) -> List[Tuple[int, int]]:
    # Merge and clamp busy intervals
    intervals = sorted([(max(day_start, s), min(day_end, e)) for s, e in busy if e > day_start and s < day_end])
    merged = []
    for s, e in intervals:
        if not merged or s > merged[-1][1]:
            merged.append([s, e])
        else:
            merged[-1][1] = max(merged[-1][1], e)

    free = []
    cur = day_start
    for s, e in merged:
        if cur < s:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < day_end:
        free.append((cur, day_end))
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

# Parameters
day = "Monday"
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
meeting_duration = 30  # minutes

# Participants' schedules and constraints
# Deborah: free all day within work hours
deborah_busy = []

# Albert busy blocks
albert_busy = [
    (to_minutes("09:00"), to_minutes("10:00")),
    (to_minutes("10:30"), to_minutes("12:00")),
    (to_minutes("15:00"), to_minutes("16:30")),
]

# Albert cannot meet after 11:00 on Monday: meeting must end by 11:00
latest_end_constraint = to_minutes("11:00")
effective_end = min(work_end, latest_end_constraint)

# Compute free intervals
deborah_free = invert_busy_to_free(deborah_busy, work_start, effective_end)
albert_free = invert_busy_to_free(albert_busy, work_start, effective_end)

# Find common free intervals
common = intersect_intervals(deborah_free, albert_free)

# Choose the earliest slot that fits the duration
start_time = end_time = None
for s, e in common:
    if e - s >= meeting_duration:
        start_time = s
        end_time = s + meeting_duration
        break

if start_time is None:
    raise RuntimeError("No suitable time found, but a solution was expected.")

print(f"{day} {{{to_hhmm(start_time)}:{to_hhmm(end_time)}}}")