from typing import List, Tuple

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

def clip_interval(interval: Tuple[int, int], win: Tuple[int, int]) -> Tuple[int, int] or None:
    s, e = interval
    ws, we = win
    s, e = max(s, ws), min(e, we)
    if s >= e:
        return None
    return (s, e)

def normalize_busy(busy: List[Tuple[int, int]], work_window: Tuple[int, int]) -> List[Tuple[int, int]]:
    clipped = []
    for iv in busy:
        c = clip_interval(iv, work_window)
        if c:
            clipped.append(c)
    if not clipped:
        return []
    clipped.sort()
    merged = [clipped[0]]
    for s, e in clipped[1:]:
        ls, le = merged[-1]
        if s <= le:
            merged[-1] = (ls, max(le, e))
        else:
            merged.append((s, e))
    return merged

def invert_to_free(busy: List[Tuple[int, int]], work_window: Tuple[int, int]) -> List[Tuple[int, int]]:
    ws, we = work_window
    if not busy:
        return [(ws, we)]
    free = []
    cur = ws
    for s, e in busy:
        if s > cur:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < we:
        free.append((cur, we))
    return free

def intersect_intervals(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
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

def find_slot(free_lists: List[List[Tuple[int, int]]], duration: int) -> Tuple[int, int] or None:
    if not free_lists:
        return None
    common = free_lists[0]
    for fl in free_lists[1:]:
        common = intersect_intervals(common, fl)
        if not common:
            return None
    for s, e in common:
        if e - s >= duration:
            return (s, s + duration)
    return None

# Input data for the task
day = "Monday"
work_window = (to_minutes("09:00"), to_minutes("17:00"))
duration = 30  # minutes

michael_busy = [
    (to_minutes("09:30"), to_minutes("10:30")),
    (to_minutes("15:00"), to_minutes("15:30")),
    (to_minutes("16:00"), to_minutes("16:30")),
]

eric_busy = []  # wide open

arthur_busy = [
    (to_minutes("09:00"), to_minutes("12:00")),
    (to_minutes("13:00"), to_minutes("15:00")),
    (to_minutes("15:30"), to_minutes("16:00")),
    (to_minutes("16:30"), to_minutes("17:00")),
]

# Process schedules
participants_busy = [
    normalize_busy(michael_busy, work_window),
    normalize_busy(eric_busy, work_window),
    normalize_busy(arthur_busy, work_window),
]

participants_free = [invert_to_free(b, work_window) for b in participants_busy]

slot = find_slot(participants_free, duration)

if slot:
    start_str = to_hhmm(slot[0])
    end_str = to_hhmm(slot[1])
    print(day)
    print(f"{{{start_str}:{end_str}}}")
else:
    print(day)
    print("{No available slot}")