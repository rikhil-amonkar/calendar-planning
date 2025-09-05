from typing import List, Tuple

# Helper functions
def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_time_str(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

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

def invert_intervals(busy: List[Tuple[int, int]], work_start: int, work_end: int) -> List[Tuple[int, int]]:
    busy = merge_intervals([(max(work_start, s), min(work_end, e)) for s, e in busy if e > work_start and s < work_end])
    free = []
    prev_end = work_start
    for s, e in busy:
        if prev_end < s:
            free.append((prev_end, s))
        prev_end = max(prev_end, e)
    if prev_end < work_end:
        free.append((prev_end, work_end))
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

def intersect_all(lists: List[List[Tuple[int, int]]]) -> List[Tuple[int, int]]:
    if not lists:
        return []
    res = lists[0]
    for lst in lists[1:]:
        res = intersect_two(res, lst)
        if not res:
            break
    return res

def find_slot(common_free: List[Tuple[int, int]], duration: int, prefer_end_before: int = None) -> Tuple[int, int]:
    # Try preferred constraint first (e.g., end <= 13:00)
    candidates = []
    if prefer_end_before is not None:
        for s, e in common_free:
            # Enumerate earliest possible start within interval to satisfy duration
            if s + duration <= e and s + duration <= prefer_end_before:
                candidates.append((s, s + duration))
        if candidates:
            return min(candidates, key=lambda x: x[0])
    # Fallback: earliest anywhere
    for s, e in common_free:
        if s + duration <= e:
            return (s, s + duration)
    return None

# Problem setup
day = "Monday"
work_start, work_end = to_minutes("9:00"), to_minutes("17:00")
duration = 30  # minutes

busy_schedules = {
    "Christine": [("9:30","10:30"), ("12:00","12:30"), ("13:00","13:30"), ("14:30","15:00"), ("16:00","16:30")],
    "Janice":    [],  # preference handled separately
    "Bobby":     [("12:00","12:30"), ("14:30","15:00")],
    "Elizabeth": [("9:00","9:30"), ("11:30","13:00"), ("13:30","14:00"), ("15:00","15:30"), ("16:00","17:00")],
    "Tyler":     [("9:00","11:00"), ("12:00","12:30"), ("13:00","13:30"), ("15:30","16:00"), ("16:30","17:00")],
    "Edward":    [("9:00","9:30"), ("10:00","11:00"), ("11:30","14:00"), ("14:30","15:30"), ("16:00","17:00")],
}

# Convert schedules to minutes and compute free intervals
free_intervals_per_person = []
for person, intervals in busy_schedules.items():
    busy_minutes = [(to_minutes(s), to_minutes(e)) for s, e in intervals]
    free_intervals = invert_intervals(busy_minutes, work_start, work_end)
    free_intervals_per_person.append(free_intervals)

# Compute common free intervals
common_free = intersect_all(free_intervals_per_person)

# Janice preference: would rather not meet after 13:00 -> aim for meeting that ends by 13:00 if possible
prefer_end_before = to_minutes("13:00")
slot = find_slot(common_free, duration, prefer_end_before=prefer_end_before)

# Fallback should not be needed per prompt, but safe-guard anyway
if slot is None:
    slot = find_slot(common_free, duration)

start_str = to_time_str(slot[0])
end_str = to_time_str(slot[1])

print(f"{{{start_str}:{end_str}}}")
print(day)