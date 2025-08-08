from typing import List, Tuple, Dict

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

def subtract_from_workday(work_start: int, work_end: int, busy: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    # Clip busy to work hours and merge
    clipped = []
    for s, e in busy:
        s = max(s, work_start)
        e = min(e, work_end)
        if s < e:
            clipped.append((s, e))
    merged_busy = merge_intervals(clipped)
    free = []
    cur = work_start
    for s, e in merged_busy:
        if cur < s:
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

def earliest_slot(common_free: List[Tuple[int, int]], duration: int) -> Tuple[int, int] or None:
    for s, e in common_free:
        if e - s >= duration:
            return (s, s + duration)
    return None

# Data
work_hours = (to_minutes("09:00"), to_minutes("17:00"))
duration = 30  # minutes
days_order = ["Monday", "Tuesday", "Wednesday"]

ronald_busy: Dict[str, List[Tuple[int, int]]] = {
    "Monday":   [(to_minutes("10:30"), to_minutes("11:00")),
                 (to_minutes("12:00"), to_minutes("12:30")),
                 (to_minutes("15:30"), to_minutes("16:00"))],
    "Tuesday":  [(to_minutes("09:00"), to_minutes("09:30")),
                 (to_minutes("12:00"), to_minutes("12:30")),
                 (to_minutes("15:30"), to_minutes("16:30"))],
    "Wednesday":[(to_minutes("09:30"), to_minutes("10:30")),
                 (to_minutes("11:00"), to_minutes("12:00")),
                 (to_minutes("12:30"), to_minutes("13:00")),
                 (to_minutes("13:30"), to_minutes("14:00")),
                 (to_minutes("16:30"), to_minutes("17:00"))],
}

amber_busy: Dict[str, List[Tuple[int, int]]] = {
    "Monday":   [(to_minutes("09:00"), to_minutes("09:30")),
                 (to_minutes("10:00"), to_minutes("10:30")),
                 (to_minutes("11:30"), to_minutes("12:00")),
                 (to_minutes("12:30"), to_minutes("14:00")),
                 (to_minutes("14:30"), to_minutes("15:00")),
                 (to_minutes("15:30"), to_minutes("17:00"))],
    "Tuesday":  [(to_minutes("09:00"), to_minutes("09:30")),
                 (to_minutes("10:00"), to_minutes("11:30")),
                 (to_minutes("12:00"), to_minutes("12:30")),
                 (to_minutes("13:30"), to_minutes("15:30")),
                 (to_minutes("16:30"), to_minutes("17:00"))],
    "Wednesday":[(to_minutes("09:00"), to_minutes("09:30")),
                 (to_minutes("10:00"), to_minutes("10:30")),
                 (to_minutes("11:00"), to_minutes("13:30")),
                 (to_minutes("15:00"), to_minutes("15:30"))],
}

# Compute earliest feasible meeting
for day in days_order:
    r_free = subtract_from_workday(*work_hours, ronald_busy.get(day, []))
    a_free = subtract_from_workday(*work_hours, amber_busy.get(day, []))
    common = intersect_intervals(r_free, a_free)
    slot = earliest_slot(common, duration)
    if slot:
        start, end = slot
        time_range = f"{{{to_hhmm(start)}:{to_hhmm(end)}}}"
        print(f"{day} {time_range}")
        break