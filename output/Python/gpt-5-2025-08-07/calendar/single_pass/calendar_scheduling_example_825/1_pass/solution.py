from typing import List, Tuple, Dict

# Helper functions
def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_time_str(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

def clip_interval(iv: Tuple[int, int], bounds: Tuple[int, int]) -> Tuple[int, int] | None:
    s, e = max(iv[0], bounds[0]), min(iv[1], bounds[1])
    return (s, e) if s < e else None

def merge_intervals(intervals: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
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

def invert_busy_to_free(busy: List[Tuple[int, int]], bounds: Tuple[int, int]) -> List[Tuple[int, int]]:
    busy_clipped = [b for b in (clip_interval(iv, bounds) for iv in busy) if b]
    busy_merged = merge_intervals(busy_clipped)
    free = []
    cur = bounds[0]
    for s, e in busy_merged:
        if cur < s:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < bounds[1]:
        free.append((cur, bounds[1]))
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

# Data
meeting_duration = 60  # minutes
work_start, work_end = to_minutes("09:00"), to_minutes("17:00")
work_bounds = (work_start, work_end)

days_order = ["Monday", "Tuesday", "Wednesday", "Thursday"]
excluded_days = {"Wednesday"}  # Philip cannot meet on Wednesday

laura_busy_str: Dict[str, List[Tuple[str, str]]] = {
    "Monday":   [("10:30","11:00"), ("12:30","13:00"), ("14:30","15:30"), ("16:00","17:00")],
    "Tuesday":  [("09:30","10:00"), ("11:00","11:30"), ("13:00","13:30"), ("14:30","15:00"), ("16:00","17:00")],
    "Wednesday":[("11:30","12:00"), ("12:30","13:00"), ("15:30","16:30")],
    "Thursday": [("10:30","11:00"), ("12:00","13:30"), ("15:00","15:30"), ("16:00","16:30")],
}

philip_busy_str: Dict[str, List[Tuple[str, str]]] = {
    "Monday":   [("09:00","17:00")],
    "Tuesday":  [("09:00","11:00"), ("11:30","12:00"), ("13:00","13:30"), ("14:00","14:30"), ("15:00","16:30")],
    "Wednesday":[("09:00","10:00"), ("11:00","12:00"), ("12:30","16:00"), ("16:30","17:00")],
    "Thursday": [("09:00","10:30"), ("11:00","12:30"), ("13:00","17:00")],
}

# Convert busy times to minutes
def convert_busy(busy_str: Dict[str, List[Tuple[str, str]]]) -> Dict[str, List[Tuple[int, int]]]:
    out: Dict[str, List[Tuple[int, int]]] = {}
    for day, slots in busy_str.items():
        out[day] = [(to_minutes(s), to_minutes(e)) for s, e in slots]
    return out

laura_busy = convert_busy(laura_busy_str)
philip_busy = convert_busy(philip_busy_str)

# Find earliest feasible meeting slot
for day in days_order:
    if day in excluded_days:
        continue

    laura_free = invert_busy_to_free(laura_busy.get(day, []), work_bounds)
    philip_free = invert_busy_to_free(philip_busy.get(day, []), work_bounds)

    common = intersect_intervals(laura_free, philip_free)
    for s, e in common:
        if e - s >= meeting_duration:
            start = s
            end = s + meeting_duration
            print(f"{day} {{{to_time_str(start)}:{to_time_str(end)}}}")
            raise SystemExit

# If no slot found (should not happen per problem statement), print nothing or raise.
raise SystemExit("No feasible meeting time found.")