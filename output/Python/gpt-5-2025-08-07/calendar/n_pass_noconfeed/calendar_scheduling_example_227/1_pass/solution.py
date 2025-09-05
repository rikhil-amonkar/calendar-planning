from typing import List, Tuple

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def from_minutes(m: int) -> str:
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

def clip_and_merge(intervals: List[Tuple[int, int]], ws: int, we: int) -> List[Tuple[int, int]]:
    clipped = []
    for s, e in intervals:
        s, e = max(ws, s), min(we, e)
        if s < e:
            clipped.append((s, e))
    return merge_intervals(clipped)

def free_from_busy(busy: List[Tuple[int, int]], ws: int, we: int) -> List[Tuple[int, int]]:
    free = []
    cursor = ws
    for s, e in busy:
        if cursor < s:
            free.append((cursor, s))
        cursor = max(cursor, e)
    if cursor < we:
        free.append((cursor, we))
    return free

def intersect_two(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    i = j = 0
    out = []
    while i < len(a) and j < len(b):
        s1, e1 = a[i]
        s2, e2 = b[j]
        s, e = max(s1, s2), min(e1, e2)
        if s < e:
            out.append((s, e))
        if e1 < e2:
            i += 1
        else:
            j += 1
    return out

def intersect_all(lists: List[List[Tuple[int, int]]]) -> List[Tuple[int, int]]:
    if not lists:
        return []
    result = lists[0]
    for lst in lists[1:]:
        result = intersect_two(result, lst)
        if not result:
            break
    return result

# Problem setup
day = "Monday"
work_start, work_end = to_minutes("09:00"), to_minutes("17:00")
duration = 30  # minutes

schedules_str = {
    "Natalie": [],
    "David": [("11:30", "12:00"), ("14:30", "15:00")],
    "Douglas": [("09:30", "10:00"), ("11:30", "12:00"), ("13:00", "13:30"), ("14:30", "15:00")],
    "Ralph": [("09:00", "09:30"), ("10:00", "11:00"), ("11:30", "12:30"), ("13:30", "15:00"), ("15:30", "16:00"), ("16:30", "17:00")],
    "Jordan": [("09:00", "10:00"), ("12:00", "12:30"), ("13:00", "13:30"), ("14:30", "15:00"), ("15:30", "17:00")],
}

# Convert to minutes
schedules = {
    person: [(to_minutes(s), to_minutes(e)) for s, e in intervals]
    for person, intervals in schedules_str.items()
}

# David does not want to meet before 14:00 on Monday
schedules["David"].append((work_start, to_minutes("14:00")))

# Build free slots for each participant within work hours
participants_free = []
for person, busy in schedules.items():
    busy_merged = clip_and_merge(busy, work_start, work_end)
    free = free_from_busy(busy_merged, work_start, work_end)
    participants_free.append(free)

# Intersect everyone’s free time
common_free = intersect_all(participants_free)

# Find the earliest slot that satisfies the duration
proposed_start = proposed_end = None
for s, e in common_free:
    if e - s >= duration:
        proposed_start = s
        proposed_end = s + duration
        break

if proposed_start is None:
    raise RuntimeError("No feasible meeting time found, but the problem statement guarantees a solution.")

time_range = f"{from_minutes(proposed_start)}:{from_minutes(proposed_end)}"
print(f"{day} {{{time_range}}}")