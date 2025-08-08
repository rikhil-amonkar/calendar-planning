from typing import List, Tuple, Dict

# Helper functions
def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m//60:02d}:{m%60:02d}"

def normalize(intervals: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    if not intervals:
        return []
    intervals = sorted(intervals)
    merged = [intervals[0]]
    for s, e in intervals[1:]:
        ls, le = merged[-1]
        if s <= le:
            merged[-1] = (ls, max(le, e))
        else:
            merged.append((s, e))
    return merged

def invert_within(bounds: Tuple[int, int], busy: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    start, end = bounds
    busy = normalize([(max(start, s), min(end, e)) for s, e in busy if e > start and s < end])
    if not busy:
        return [(start, end)]
    free = []
    cur = start
    for s, e in busy:
        if cur < s:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < end:
        free.append((cur, end))
    return free

def intersect_intervals(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    i, j = 0, 0
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

# Data
days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
work_bounds = (to_minutes("09:00"), to_minutes("17:00"))
duration = 30  # minutes

betty_busy: Dict[str, List[Tuple[int, int]]] = {
    "Monday":    [(to_minutes("10:00"), to_minutes("10:30")),
                  (to_minutes("13:30"), to_minutes("14:00")),
                  (to_minutes("15:00"), to_minutes("15:30")),
                  (to_minutes("16:00"), to_minutes("16:30"))],
    "Tuesday":   [(to_minutes("09:00"), to_minutes("09:30")),
                  (to_minutes("11:30"), to_minutes("12:00")),
                  (to_minutes("12:30"), to_minutes("13:00")),
                  (to_minutes("13:30"), to_minutes("14:00")),
                  (to_minutes("16:30"), to_minutes("17:00"))],
    "Wednesday": [(to_minutes("09:30"), to_minutes("10:30")),
                  (to_minutes("13:00"), to_minutes("13:30")),
                  (to_minutes("14:00"), to_minutes("14:30"))],
    "Thursday":  [(to_minutes("09:30"), to_minutes("10:00")),
                  (to_minutes("11:30"), to_minutes("12:00")),
                  (to_minutes("14:00"), to_minutes("14:30")),
                  (to_minutes("15:00"), to_minutes("15:30")),
                  (to_minutes("16:30"), to_minutes("17:00"))],
}

scott_busy: Dict[str, List[Tuple[int, int]]] = {
    "Monday":    [(to_minutes("09:30"), to_minutes("15:00")),
                  (to_minutes("15:30"), to_minutes("16:00")),
                  (to_minutes("16:30"), to_minutes("17:00"))],
    "Tuesday":   [(to_minutes("09:00"), to_minutes("09:30")),
                  (to_minutes("10:00"), to_minutes("11:00")),
                  (to_minutes("11:30"), to_minutes("12:00")),
                  (to_minutes("12:30"), to_minutes("13:30")),
                  (to_minutes("14:00"), to_minutes("15:00")),
                  (to_minutes("16:00"), to_minutes("16:30"))],
    "Wednesday": [(to_minutes("09:30"), to_minutes("12:30")),
                  (to_minutes("13:00"), to_minutes("13:30")),
                  (to_minutes("14:00"), to_minutes("14:30")),
                  (to_minutes("15:00"), to_minutes("15:30")),
                  (to_minutes("16:00"), to_minutes("16:30"))],
    "Thursday":  [(to_minutes("09:00"), to_minutes("09:30")),
                  (to_minutes("10:00"), to_minutes("10:30")),
                  (to_minutes("11:00"), to_minutes("12:00")),
                  (to_minutes("12:30"), to_minutes("13:00")),
                  (to_minutes("15:00"), to_minutes("16:00")),
                  (to_minutes("16:30"), to_minutes("17:00"))],
}

# Constraints:
# Betty cannot meet on Monday at all; on Tuesday and Thursday before 15:00
for d in days:
    if d == "Monday":
        betty_busy[d] = normalize(betty_busy[d] + [(work_bounds[0], work_bounds[1])])
    elif d in ("Tuesday", "Thursday"):
        betty_busy[d] = normalize(betty_busy[d] + [(work_bounds[0], to_minutes("15:00"))])

# Build free intervals
betty_free = {d: invert_within(work_bounds, betty_busy[d]) for d in days}
scott_free = {d: invert_within(work_bounds, scott_busy[d]) for d in days}

# Find candidate slots per day that meet duration
candidates = []
for d in days:
    overlap = intersect_intervals(betty_free[d], scott_free[d])
    # slice into discrete 30-min blocks aligned to minutes
    for s, e in overlap:
        cur = s
        while cur + duration <= e:
            candidates.append((d, cur, cur + duration))
            cur += duration  # step in 30-min increments

# Prefer non-Wednesday slots if available, otherwise Wednesday
non_wed = [c for c in candidates if c[0] != "Wednesday"]
chosen = None
if non_wed:
    chosen = min(non_wed, key=lambda x: (days.index(x[0]), x[1]))
else:
    wed = [c for c in candidates if c[0] == "Wednesday"]
    if wed:
        chosen = min(wed, key=lambda x: x[1])

# Output result
if chosen:
    day, s, e = chosen
    print(day)
    print(f"{to_hhmm(s)}:{to_hhmm(e)}")
else:
    print("No available slot found")