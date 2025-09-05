from typing import List, Tuple

# Meeting configuration
DAY = "Monday"
WORK_START = "09:00"
WORK_END = "17:00"
MEETING_MINUTES = 30

# Participants' busy schedules for Monday
busy_schedules = {
    "Jacob":  [("13:30", "14:00"), ("14:30", "15:00")],
    "Diana":  [("09:30", "10:00"), ("11:30", "12:00"), ("13:00", "13:30"), ("16:00", "16:30")],
    "Adam":   [("09:30", "10:30"), ("11:00", "12:30"), ("15:30", "16:00")],
    "Angela": [("09:30", "10:00"), ("10:30", "12:00"), ("13:00", "15:30"), ("16:00", "16:30")],
    "Dennis": [("09:00", "09:30"), ("10:30", "11:30"), ("13:00", "15:00"), ("16:30", "17:00")],
}

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

def clip_and_merge(intervals: List[Tuple[int, int]], window: Tuple[int, int]) -> List[Tuple[int, int]]:
    w_start, w_end = window
    clipped = []
    for s, e in intervals:
        if e <= w_start or s >= w_end:
            continue
        clipped.append((max(s, w_start), min(e, w_end)))
    if not clipped:
        return []
    clipped.sort()
    merged = [clipped[0]]
    for s, e in clipped[1:]:
        last_s, last_e = merged[-1]
        if s <= last_e:
            merged[-1] = (last_s, max(last_e, e))
        else:
            merged.append((s, e))
    return merged

def invert_intervals(busy: List[Tuple[int, int]], window: Tuple[int, int]) -> List[Tuple[int, int]]:
    w_start, w_end = window
    merged_busy = clip_and_merge(busy, window)
    free = []
    prev = w_start
    for s, e in merged_busy:
        if s > prev:
            free.append((prev, s))
        prev = max(prev, e)
    if prev < w_end:
        free.append((prev, w_end))
    return free

def intersect(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
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

def find_slot(schedules: dict, work_start: str, work_end: str, duration_minutes: int):
    window = (to_minutes(work_start), to_minutes(work_end))
    # Build free intervals for each participant
    common_free = None
    for person, busy in schedules.items():
        busy_minutes = [(to_minutes(s), to_minutes(e)) for s, e in busy]
        free = invert_intervals(busy_minutes, window)
        if common_free is None:
            common_free = free
        else:
            common_free = intersect(common_free, free)
        if not common_free:
            break
    if not common_free:
        return None
    # Find the earliest interval with sufficient length
    for s, e in common_free:
        if e - s >= duration_minutes:
            return (s, s + duration_minutes)
    return None

slot = find_slot(busy_schedules, WORK_START, WORK_END, MEETING_MINUTES)

if slot is None:
    # As per prompt, a solution exists; this is a fallback.
    print(DAY)
    print("{No available slot}")
else:
    start_str = to_hhmm(slot[0])
    end_str = to_hhmm(slot[1])
    print(DAY)
    print(f"{{{start_str}:{end_str}}}")