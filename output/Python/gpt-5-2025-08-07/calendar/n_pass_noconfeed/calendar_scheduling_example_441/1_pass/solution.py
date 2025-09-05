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

def invert_intervals(busy: List[Tuple[int, int]], start: int, end: int) -> List[Tuple[int, int]]:
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

def intersect_intervals(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    i, j = 0, 0
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

# Problem setup
day = "Monday"
work_hours = ("09:00", "17:00")
meeting_duration = 30  # minutes

schedules = {
    "Joan":    [("11:30", "12:00"), ("14:30", "15:00")],
    "Megan":   [("09:00", "10:00"), ("14:00", "14:30"), ("16:00", "16:30")],
    "Austin":  [],  # free all day
    "Betty":   [("09:30", "10:00"), ("11:30", "12:00"), ("13:30", "14:00"), ("16:00", "16:30")],
    "Judith":  [("09:00", "11:00"), ("12:00", "13:00"), ("14:00", "15:00")],
    "Terry":   [("09:30", "10:00"), ("11:30", "12:30"), ("13:00", "14:00"), ("15:00", "15:30"), ("16:00", "17:00")],
    "Kathryn": [("09:30", "10:00"), ("10:30", "11:00"), ("11:30", "13:00"), ("14:00", "16:00"), ("16:30", "17:00")],
}

ws, we = map(to_minutes, work_hours)

# Compute each participant's free intervals within work hours
all_free = [(ws, we)]
for person, busy_str in schedules.items():
    busy = [(to_minutes(s), to_minutes(e)) for s, e in busy_str]
    free = invert_intervals(busy, ws, we)
    all_free = intersect_intervals(all_free, free)
    if not all_free:
        break

# Find the earliest interval that fits the meeting duration
start_time, end_time = None, None
for s, e in all_free:
    if e - s >= meeting_duration:
        start_time = s
        end_time = s + meeting_duration
        break

if start_time is None:
    raise RuntimeError("No suitable time found, but the problem guarantees a solution.")

time_range = f"{to_hhmm(start_time)}:{to_hhmm(end_time)}"

# Output: day and time range enclosed in braces
print(day)
print(f"{{{time_range}}}")