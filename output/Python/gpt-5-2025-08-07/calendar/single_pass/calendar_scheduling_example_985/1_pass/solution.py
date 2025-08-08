from typing import List, Tuple, Dict

# Helper functions
def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_time_str(m: int) -> str:
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

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

def subtract_from_range(range_interval: Tuple[int, int], busy: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    start, end = range_interval
    if start >= end:
        return []
    free = []
    cursor = start
    for b_start, b_end in merge_intervals([b for b in busy if not (b_end <= start or b_start >= end)]):
        if b_start > cursor:
            free.append((cursor, min(b_start, end)))
        cursor = max(cursor, b_end)
        if cursor >= end:
            break
    if cursor < end:
        free.append((cursor, end))
    return [(s, e) for s, e in free if e > s]

def intersect_intervals(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    i = j = 0
    res = []
    a = sorted(a)
    b = sorted(b)
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
work_hours = (to_minutes("09:00"), to_minutes("17:00"))
duration = 60  # minutes

diane_busy_str: Dict[str, List[Tuple[str, str]]] = {
    "Monday":    [("12:00", "12:30"), ("15:00", "15:30")],
    "Tuesday":   [("10:00", "11:00"), ("11:30", "12:00"), ("12:30", "13:00"), ("16:00", "17:00")],
    "Wednesday": [("09:00", "09:30"), ("14:30", "15:00"), ("16:30", "17:00")],
    "Thursday":  [("15:30", "16:30")],
    "Friday":    [("09:30", "11:30"), ("14:30", "15:00"), ("16:00", "17:00")],
}
matt_busy_str: Dict[str, List[Tuple[str, str]]] = {
    "Monday":    [("09:00", "10:00"), ("10:30", "17:00")],
    "Tuesday":   [("09:00", "17:00")],
    "Wednesday": [("09:00", "11:00"), ("12:00", "14:30"), ("16:00", "17:00")],
    "Thursday":  [("09:00", "16:00")],
    "Friday":    [("09:00", "17:00")],
}

# Convert busy times to minutes
def convert_busy(busy_str: Dict[str, List[Tuple[str, str]]]) -> Dict[str, List[Tuple[int, int]]]:
    out = {}
    for day in days:
        intervals = busy_str.get(day, [])
        out[day] = [(to_minutes(s), to_minutes(e)) for s, e in intervals]
    return out

diane_busy = convert_busy(diane_busy_str)
matt_busy = convert_busy(matt_busy_str)

# Preference: Matthew would rather not meet on Wednesday before 12:30
weds_pref_start = to_minutes("12:30")

def apply_wednesday_preference(intervals: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    adjusted = []
    for s, e in intervals:
        ns = max(s, weds_pref_start)
        if ns < e:
            adjusted.append((ns, e))
    return adjusted

# Search for earliest valid slot
for day in days:
    d_free = subtract_from_range(work_hours, diane_busy.get(day, []))
    m_free = subtract_from_range(work_hours, matt_busy.get(day, []))
    common = intersect_intervals(d_free, m_free)
    if day == "Wednesday":
        common = apply_wednesday_preference(common)
    for s, e in common:
        if e - s >= duration:
            start = s
            end = s + duration
            print(f"{day} {{{to_time_str(start)}:{to_time_str(end)}}}")
            raise SystemExit

# If somehow none found (should not happen per problem statement)
print("No suitable time found")