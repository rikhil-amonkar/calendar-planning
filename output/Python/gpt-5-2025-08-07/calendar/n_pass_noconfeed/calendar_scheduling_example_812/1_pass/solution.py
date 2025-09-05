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

def subtract_intervals(base: Tuple[int, int], blocks: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    start, end = base
    free = []
    cursor = start
    for b_start, b_end in merge_intervals(blocks):
        if b_end <= cursor:
            continue
        if b_start > end:
            break
        if b_start > cursor:
            free.append((cursor, min(b_start, end)))
        cursor = max(cursor, b_end)
        if cursor >= end:
            break
    if cursor < end:
        free.append((cursor, end))
    return free

def intersect_two(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
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
meeting_duration = 30  # minutes

mary_busy_raw: Dict[str, List[Tuple[str, str]]] = {
    "Tuesday": [("10:00", "10:30"), ("15:30", "16:00")],
    "Wednesday": [("9:30", "10:00"), ("15:00", "15:30")],
    "Thursday": [("9:00", "10:00"), ("10:30", "11:30")],
}
alexis_busy_raw: Dict[str, List[Tuple[str, str]]] = {
    "Monday": [("9:00", "10:00"), ("10:30", "12:00"), ("12:30", "16:30")],
    "Tuesday": [("9:00", "10:00"), ("10:30", "11:30"), ("12:00", "15:30"), ("16:00", "17:00")],
    "Wednesday": [("9:00", "11:00"), ("11:30", "17:00")],
    "Thursday": [("10:00", "12:00"), ("14:00", "14:30"), ("15:30", "16:00"), ("16:30", "17:00")],
}

def to_minutes_intervals(raw: Dict[str, List[Tuple[str, str]]]) -> Dict[str, List[Tuple[int, int]]]:
    conv = {}
    for d in days:
        intervals = raw.get(d, [])
        conv[d] = [(to_minutes(s), to_minutes(e)) for s, e in intervals]
    return conv

mary_busy = to_minutes_intervals(mary_busy_raw)
alexis_busy = to_minutes_intervals(alexis_busy_raw)

# Find earliest slot
earliest_day = None
earliest_slot = None

for d in days:
    base = (work_start, work_end)
    mary_free = subtract_intervals(base, mary_busy.get(d, []))
    alexis_free = subtract_intervals(base, alexis_busy.get(d, []))
    common = intersect_two(mary_free, alexis_free)
    # Find earliest segment of at least meeting_duration
    for s, e in common:
        if e - s >= meeting_duration:
            earliest_day = d
            earliest_slot = (s, s + meeting_duration)
            break
    if earliest_slot:
        break

if earliest_day and earliest_slot:
    start_str = to_hhmm(earliest_slot[0])
    end_str = to_hhmm(earliest_slot[1])
    print(f"{earliest_day}")
    print(f"{{{start_str}:{end_str}}}")
else:
    # Fallback (should not occur given the problem statement)
    print("No available slot found within the constraints.")