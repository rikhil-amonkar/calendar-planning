from typing import List, Tuple

# Utilities
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

def complement_intervals(window: Tuple[int, int], busy: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    start, end = window
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

def intersect_two(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    i = j = 0
    inter = []
    while i < len(a) and j < len(b):
        s = max(a[i][0], b[j][0])
        e = min(a[i][1], b[j][1])
        if s < e:
            inter.append((s, e))
        if a[i][1] < b[j][1]:
            i += 1
        else:
            j += 1
    return inter

def intersect_all(lists: List[List[Tuple[int, int]]]) -> List[Tuple[int, int]]:
    if not lists:
        return []
    inter = lists[0]
    for lst in lists[1:]:
        inter = intersect_two(inter, lst)
        if not inter:
            break
    return inter

# Inputs
day = "Monday"
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
window = (work_start, work_end)
duration = 30  # minutes

busy = {
    "Kimberly": [("10:00","10:30"), ("11:00","12:00"), ("16:00","16:30")],
    "Megan":    [],  # no meetings
    "Marie":    [("10:00","11:00"), ("11:30","15:00"), ("16:00","16:30")],
    "Diana":    [("09:30","10:00"), ("10:30","14:30"), ("15:30","17:00")],
}

# Convert busy times to minutes
busy_minutes = {
    person: [(to_minutes(s), to_minutes(e)) for s, e in intervals]
    for person, intervals in busy.items()
}

# Compute free intervals per participant within the work window
free_intervals = {
    person: complement_intervals(window, intervals)
    for person, intervals in busy_minutes.items()
}

# Find common free intervals
common_free = intersect_all(list(free_intervals.values()))

# Filter intervals that can fit the required duration, split into exact slots if needed
candidates = []
for s, e in common_free:
    if e - s >= duration:
        candidates.append((s, s + duration))  # choose the earliest possible within each block

# Apply preference: Megan prefers not before 10:00
preference_threshold = to_minutes("10:00")
preferred = [slot for slot in candidates if slot[0] >= preference_threshold]

chosen = None
if preferred:
    chosen = min(preferred, key=lambda x: x[0])
elif candidates:
    chosen = min(candidates, key=lambda x: x[0])

# Output
if chosen:
    start_str = to_hhmm(chosen[0])
    end_str = to_hhmm(chosen[1])
    print(f"{start_str}:{end_str}")
    print(day)
else:
    # Fallback (should not happen per problem statement)
    print("No available slot")
    print(day)