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

def invert_intervals(busy: List[Tuple[int, int]], work_start: int, work_end: int) -> List[Tuple[int, int]]:
    free = []
    cur = work_start
    for s, e in busy:
        s = max(s, work_start)
        e = min(e, work_end)
        if e <= work_start or s >= work_end:
            continue
        if s > cur:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < work_end:
        free.append((cur, work_end))
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

# Input data
work_hours = ("09:00", "17:00")
duration_min = 30
days = ["Monday", "Tuesday", "Wednesday"]

nancy_busy = {
    "Monday":    [("10:00","10:30"), ("11:30","12:30"), ("13:30","14:00"), ("14:30","15:30"), ("16:00","17:00")],
    "Tuesday":   [("09:30","10:30"), ("11:00","11:30"), ("12:00","12:30"), ("13:00","13:30"), ("15:30","16:00")],
    "Wednesday": [("10:00","11:30"), ("13:30","16:00")],
}

jose_busy = {
    "Monday":    [("09:00","17:00")],
    "Tuesday":   [("09:00","17:00")],
    "Wednesday": [("09:00","09:30"), ("10:00","12:30"), ("13:30","14:30"), ("15:00","17:00")],
}

ws = to_minutes(work_hours[0])
we = to_minutes(work_hours[1])

def to_min_intervals(intervals: List[Tuple[str, str]]) -> List[Tuple[int, int]]:
    return [(to_minutes(s), to_minutes(e)) for s, e in intervals]

# Find earliest slot
for day in days:
    n_busy = merge_intervals(to_min_intervals(nancy_busy.get(day, [])))
    j_busy = merge_intervals(to_min_intervals(jose_busy.get(day, [])))

    n_free = invert_intervals(n_busy, ws, we)
    j_free = invert_intervals(j_busy, ws, we)

    common = intersect_intervals(n_free, j_free)

    for s, e in common:
        if e - s >= duration_min:
            start = s
            end = s + duration_min
            print(day)
            print(f"{{{to_hhmm(start)}:{to_hhmm(end)}}}")
            raise SystemExit

# Fallback (should not occur per problem statement)
print("No available slot found")