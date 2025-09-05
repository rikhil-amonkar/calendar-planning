from typing import List, Tuple, Dict

# Helpers
def t(h: int, m: int) -> int:
    return h * 60 + m

def m2s(minutes: int) -> str:
    return f"{minutes // 60:02d}:{minutes % 60:02d}"

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

def invert_within_work(busy: List[Tuple[int, int]], work: Tuple[int, int]) -> List[Tuple[int, int]]:
    busy = merge_intervals([b for b in busy if b[1] > work[0] and b[0] < work[1]])
    free: List[Tuple[int, int]] = []
    cur = work[0]
    for s, e in busy:
        if s > cur:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < work[1]:
        free.append((cur, work[1]))
    return free

def intersect(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    i = j = 0
    res: List[Tuple[int, int]] = []
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
days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
preferred_day_order = ["Tuesday", "Wednesday", "Thursday", "Friday", "Monday"]  # avoid Monday if possible
work_hours = (t(9, 0), t(17, 0))
duration = 60  # minutes

brian_busy: Dict[str, List[Tuple[int, int]]] = {
    "Monday":    [(t(9,30), t(10,0)), (t(12,30), t(14,30)), (t(15,30), t(16,0))],
    "Tuesday":   [(t(9,0), t(9,30))],
    "Wednesday": [(t(12,30), t(14,0)), (t(16,30), t(17,0))],
    "Thursday":  [(t(11,0), t(11,30)), (t(13,0), t(13,30)), (t(16,30), t(17,0))],
    "Friday":    [(t(9,30), t(10,0)), (t(10,30), t(11,0)), (t(13,0), t(13,30)), (t(15,0), t(16,0)), (t(16,30), t(17,0))],
}

julia_busy: Dict[str, List[Tuple[int, int]]] = {
    "Monday":    [(t(9,0), t(10,0)), (t(11,0), t(11,30)), (t(12,30), t(13,0)), (t(15,30), t(16,0))],
    "Tuesday":   [(t(13,0), t(14,0)), (t(16,0), t(16,30))],
    "Wednesday": [(t(9,0), t(11,30)), (t(12,0), t(12,30)), (t(13,0), t(17,0))],
    "Thursday":  [(t(9,0), t(10,30)), (t(11,0), t(17,0))],
    "Friday":    [(t(9,0), t(10,0)), (t(10,30), t(11,30)), (t(12,30), t(14,0)), (t(14,30), t(15,0)), (t(15,30), t(16,0))],
}

# Compute free slots per day
brian_free = {d: invert_within_work(brian_busy.get(d, []), work_hours) for d in days}
julia_free = {d: invert_within_work(julia_busy.get(d, []), work_hours) for d in days}

# Search earliest slot honoring preference (avoid Monday)
meeting_day = None
meeting_start = None

for d in preferred_day_order:
    overlaps = intersect(brian_free[d], julia_free[d])
    for s, e in overlaps:
        if e - s >= duration:
            meeting_day = d
            meeting_start = s
            break
    if meeting_day is not None:
        break

# Fallback (shouldn't be needed given problem guarantees)
if meeting_day is None:
    for d in days:
        overlaps = intersect(brian_free[d], julia_free[d])
        for s, e in overlaps:
            if e - s >= duration:
                meeting_day = d
                meeting_start = s
                break
        if meeting_day is not None:
            break

# Output
if meeting_day is None:
    print("No available slot found")
else:
    start_str = m2s(meeting_start)
    end_str = m2s(meeting_start + duration)
    print(f"{meeting_day} {{{start_str}:{end_str}}}")