from typing import List, Tuple

# Helper functions
def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_str(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

def clamp(intervals: List[Tuple[int, int]], bounds: Tuple[int, int]) -> List[Tuple[int, int]]:
    start, end = bounds
    clamped = []
    for s, e in intervals:
        s2, e2 = max(s, start), min(e, end)
        if s2 < e2:
            clamped.append((s2, e2))
    return sorted(clamped)

def invert_busy_to_free(busy: List[Tuple[int, int]], work: Tuple[int, int]) -> List[Tuple[int, int]]:
    ws, we = work
    busy = clamp(sorted(busy), work)
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

def find_slot(free_intersections: List[Tuple[int, int]], duration: int, preferred_start: int = None) -> Tuple[int, int]:
    # Try preferred window first (start >= preferred_start) if provided
    if preferred_start is not None:
        for s, e in free_intersections:
            if e - max(s, preferred_start) >= duration:
                return max(s, preferred_start), max(s, preferred_start) + duration
    # Fallback: earliest anywhere
    for s, e in free_intersections:
        if e - s >= duration:
            return s, s + duration
    return None

# Inputs
day = "Monday"
work_hours = (to_minutes("9:00"), to_minutes("17:00"))
duration = 30  # minutes
angela_prefer_after = to_minutes("15:00")

calendars_busy = {
    "Katherine": [("12:00","12:30"), ("13:00","14:30")],
    "Rebecca":  [],
    "Julie":    [("9:00","9:30"), ("10:30","11:00"), ("13:30","14:00"), ("15:00","15:30")],
    "Angela":   [("9:00","10:00"), ("10:30","11:00"), ("11:30","14:00"), ("14:30","15:00"), ("16:30","17:00")],
    "Nicholas": [("9:30","11:00"), ("11:30","13:30"), ("14:00","16:00"), ("16:30","17:00")],
    "Carl":     [("9:00","11:00"), ("11:30","12:30"), ("13:00","14:30"), ("15:00","16:00"), ("16:30","17:00")],
}

# Convert to minutes
busy_minutes = {
    person: [(to_minutes(s), to_minutes(e)) for s, e in intervals]
    for person, intervals in calendars_busy.items()
}

# Compute free intervals per participant within work hours
free_per_person = [
    invert_busy_to_free(busy_minutes[person], work_hours)
    for person in ["Katherine", "Rebecca", "Julie", "Angela", "Nicholas", "Carl"]
]

# Intersect everyone's free intervals
common_free = intersect_all(free_per_person)

# Find a 30-minute slot respecting Angela's preference to avoid before 15:00 if possible
slot = find_slot(common_free, duration, preferred_start=angela_prefer_after)

# Fallback without preference (shouldn't be needed per problem statement)
if slot is None:
    slot = find_slot(common_free, duration)

start_str, end_str = to_str(slot[0]), to_str(slot[1])

# Output in required format
print(f"{{{start_str}:{end_str}}}")
print(day)