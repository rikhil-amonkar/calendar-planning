from typing import List, Tuple

# Helper functions
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

def invert_busy_to_free(busy: List[Tuple[int, int]], day_start: int, day_end: int) -> List[Tuple[int, int]]:
    busy = [(max(day_start, s), min(day_end, e)) for s, e in busy if e > day_start and s < day_end]
    busy = merge_intervals(busy)
    free = []
    cur = day_start
    for s, e in busy:
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

# Data
days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
work_start, work_end = to_minutes("09:00"), to_minutes("17:00")
one_hour = 60

megan_busy_str = {
    "Monday":    [("13:00","13:30"), ("14:00","15:30")],
    "Tuesday":   [("09:00","09:30"), ("12:00","12:30"), ("16:00","17:00")],
    "Wednesday": [("09:30","10:00"), ("10:30","11:30"), ("12:30","14:00"), ("16:00","16:30")],
    "Thursday":  [("13:30","14:30"), ("15:00","15:30")],
}
daniel_busy_str = {
    "Monday":    [("10:00","11:30"), ("12:30","15:00")],
    "Tuesday":   [("09:00","10:00"), ("10:30","17:00")],
    "Wednesday": [("09:00","10:00"), ("10:30","11:30"), ("12:00","17:00")],
    "Thursday":  [("09:00","12:00"), ("12:30","14:30"), ("15:00","15:30"), ("16:00","17:00")],
}

# Convert to minutes
megan_busy = {d: [(to_minutes(s), to_minutes(e)) for s, e in megan_busy_str[d]] for d in days}
daniel_busy = {d: [(to_minutes(s), to_minutes(e)) for s, e in daniel_busy_str[d]] for d in days}

# Find earliest feasible slot
for day in days:
    megan_free = invert_busy_to_free(megan_busy[day], work_start, work_end)
    daniel_free = invert_busy_to_free(daniel_busy[day], work_start, work_end)
    common = intersect_intervals(megan_free, daniel_free)
    for s, e in common:
        if e - s >= one_hour:
            start, end = s, s + one_hour
            print(f"{day} {{{to_hhmm(start)}:{to_hhmm(end)}}}")
            raise SystemExit

# If no slot found (should not happen per problem statement)
print("No available slot found")