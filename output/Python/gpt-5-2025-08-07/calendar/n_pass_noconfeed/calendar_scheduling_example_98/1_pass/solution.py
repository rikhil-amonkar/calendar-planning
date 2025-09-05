from typing import List, Tuple

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

def clamp(interval: Tuple[int, int], bounds: Tuple[int, int]) -> Tuple[int, int]:
    s, e = interval
    bs, be = bounds
    return max(s, bs), min(e, be)

def merge_intervals(intervals: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    if not intervals:
        return []
    intervals = sorted(intervals)
    merged = [list(intervals[0])]
    for s, e in intervals[1:]:
        if s <= merged[-1][1]:
            merged[-1][1] = max(merged[-1][1], e)
        else:
            merged.append([s, e])
    return [tuple(x) for x in merged]

def subtract_from_window(window: Tuple[int, int], blocks: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    ws, we = window
    free = []
    cur = ws
    for s, e in blocks:
        if e <= cur:
            continue
        if s > cur:
            free.append((cur, s))
        cur = max(cur, e)
        if cur >= we:
            break
    if cur < we:
        free.append((cur, we))
    return free

def find_slot(free: List[Tuple[int, int]], duration: int) -> Tuple[int, int]:
    for s, e in free:
        if e - s >= duration:
            return s, s + duration
    return None

# Problem setup
day = "Monday"
work_start, work_end = to_minutes("09:00"), to_minutes("17:00")
meeting_duration = 30  # minutes

# Busy schedules
juan_busy = [
    ("09:00", "10:30"),
    ("15:30", "16:00"),
    # Juan cannot meet after 16:00 on Monday
    ("16:00", "17:00"),
]

marilyn_busy = [
    ("11:00", "11:30"),
    ("12:30", "13:00"),
]

ronald_busy = [
    ("09:00", "10:30"),
    ("12:00", "12:30"),
    ("13:00", "13:30"),
    ("14:00", "16:30"),
]

# Convert and clamp to work hours
all_busy = []
for s, e in juan_busy + marilyn_busy + ronald_busy:
    cs, ce = clamp((to_minutes(s), to_minutes(e)), (work_start, work_end))
    if cs < ce:
        all_busy.append((cs, ce))

# Merge all busy times (union across participants)
merged_busy = merge_intervals(all_busy)

# Compute free times where everyone is available
work_window = (work_start, work_end)
free_windows = subtract_from_window(work_window, merged_busy)

# Find earliest slot of required duration
slot = find_slot(free_windows, meeting_duration)

if slot:
    start_str, end_str = to_hhmm(slot[0]), to_hhmm(slot[1])
    print(f"{{{start_str}:{end_str}}} {day}")
else:
    print(f"No available {meeting_duration}-minute slot on {day}.")