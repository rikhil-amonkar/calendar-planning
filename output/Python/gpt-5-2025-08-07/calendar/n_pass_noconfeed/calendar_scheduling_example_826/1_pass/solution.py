from typing import List, Tuple

# Helper functions
def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

def merge_intervals(intervals: List[Tuple[int,int]]) -> List[Tuple[int,int]]:
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

def invert_intervals(busy: List[Tuple[int,int]], start: int, end: int) -> List[Tuple[int,int]]:
    busy = merge_intervals([(max(start, s), min(end, e)) for s, e in busy if e > start and s < end])
    free = []
    cur = start
    for s, e in busy:
        if cur < s:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < end:
        free.append((cur, end))
    return free

def intersect_intervals(a: List[Tuple[int,int]], b: List[Tuple[int,int]]) -> List[Tuple[int,int]]:
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

def earliest_slot(free: List[Tuple[int,int]], duration: int) -> Tuple[int,int] or None:
    for s, e in free:
        if e - s >= duration:
            return (s, s + duration)
    return None

# Work hours and duration
WORK_START = to_minutes("09:00")
WORK_END   = to_minutes("17:00")
DURATION = 30  # minutes

days = ["Monday", "Tuesday", "Wednesday", "Thursday"]

# Schedules (busy intervals) for participants
# Cheryl is free all week (no busy intervals)
cheryl_busy = {
    "Monday": [],
    "Tuesday": [],
    "Wednesday": [],
    "Thursday": []
}

# James' busy intervals
james_busy = {
    "Monday":    [("09:00","09:30"), ("10:30","11:00"), ("12:30","13:00"), ("14:30","15:30"), ("16:30","17:00")],
    "Tuesday":   [("09:00","11:00"), ("11:30","12:00"), ("12:30","15:30"), ("16:00","17:00")],
    "Wednesday": [("10:00","11:00"), ("12:00","13:00"), ("13:30","16:00")],
    "Thursday":  [("09:30","11:30"), ("12:00","12:30"), ("13:00","13:30"), ("14:00","14:30"), ("16:30","17:00")]
}

# Convert busy times to minutes
def convert_day(busy_list):
    return [(to_minutes(s), to_minutes(e)) for s, e in busy_list]

james_busy_min = {d: convert_day(lst) for d, lst in james_busy.items()}
cheryl_busy_min = {d: convert_day(lst) for d, lst in cheryl_busy.items()}

# Preferences: Cheryl would rather not meet on Wednesday or Thursday.
preferred_order = ["Monday", "Tuesday", "Wednesday", "Thursday"]

# Find earliest feasible slot following preferences
for day in preferred_order:
    # Compute free intervals within work hours for each participant
    cheryl_free = invert_intervals(cheryl_busy_min[day], WORK_START, WORK_END)
    james_free = invert_intervals(james_busy_min[day], WORK_START, WORK_END)
    # Intersection of free intervals
    common_free = intersect_intervals(cheryl_free, james_free)
    slot = earliest_slot(common_free, DURATION)
    if slot:
        start_str = to_hhmm(slot[0])
        end_str = to_hhmm(slot[1])
        print(day)
        print(f"{{{start_str}:{end_str}}}")
        break