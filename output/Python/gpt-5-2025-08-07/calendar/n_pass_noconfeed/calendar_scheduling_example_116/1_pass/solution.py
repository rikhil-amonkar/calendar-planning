# Meeting scheduler for Adam, John, Stephanie, and Anna on Monday

from typing import List, Tuple

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_str(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

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

def complement_intervals(busy: List[Tuple[int, int]], window: Tuple[int, int]) -> List[Tuple[int, int]]:
    ws, we = window
    busy = merge_intervals([(max(ws, s), min(we, e)) for s, e in busy if e > ws and s < we])
    free = []
    cur = ws
    for s, e in busy:
        if cur < s:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < we:
        free.append((cur, we))
    return free

def intersect_two(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
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

def intersect_all(lists: List[List[Tuple[int, int]]]) -> List[Tuple[int, int]]:
    if not lists:
        return []
    res = lists[0]
    for lst in lists[1:]:
        res = intersect_two(res, lst)
        if not res:
            break
    return res

# Parameters
day = "Monday"
work_window = (to_minutes("09:00"), to_minutes("17:00"))
duration = 30  # minutes
earliest_start_pref = to_minutes("14:30")  # Anna would rather not meet before 14:30

# Busy schedules
adam_busy = [(to_minutes("14:00"), to_minutes("15:00"))]
john_busy = [
    (to_minutes("13:00"), to_minutes("13:30")),
    (to_minutes("14:00"), to_minutes("14:30")),
    (to_minutes("15:30"), to_minutes("16:00")),
    (to_minutes("16:30"), to_minutes("17:00")),
]
stephanie_busy = [
    (to_minutes("09:30"), to_minutes("10:00")),
    (to_minutes("10:30"), to_minutes("11:00")),
    (to_minutes("11:30"), to_minutes("16:00")),
    (to_minutes("16:30"), to_minutes("17:00")),
]
anna_busy = [
    (to_minutes("09:30"), to_minutes("10:00")),
    (to_minutes("12:00"), to_minutes("12:30")),
    (to_minutes("13:00"), to_minutes("15:30")),
    (to_minutes("16:30"), to_minutes("17:00")),
]
# Apply Anna's preference as additional busy time before 14:30
anna_busy_with_pref = anna_busy + [(work_window[0], earliest_start_pref)]

# Compute free intervals
adam_free = complement_intervals(adam_busy, work_window)
john_free = complement_intervals(john_busy, work_window)
stephanie_free = complement_intervals(stephanie_busy, work_window)
anna_free = complement_intervals(anna_busy_with_pref, work_window)

# Find common availability
common_free = intersect_all([adam_free, john_free, stephanie_free, anna_free])

# Locate the earliest slot of required duration
start_time = end_time = None
for s, e in common_free:
    candidate_start = max(s, earliest_start_pref)
    if candidate_start + duration <= e:
        start_time = candidate_start
        end_time = candidate_start + duration
        break

if start_time is None:
    raise SystemExit("No suitable meeting time found.")

# Output: day and time range in {HH:MM:HH:MM}
print(day)
print(f"{{{to_str(start_time)}:{to_str(end_time)}}}")