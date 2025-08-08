from typing import List, Tuple, Dict

# Utilities
def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m//60:02d}:{m%60:02d}"

def merge_intervals(intervals: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    if not intervals: return []
    intervals.sort()
    merged = [intervals[0]]
    for s, e in intervals[1:]:
        ls, le = merged[-1]
        if s <= le:
            merged[-1] = (ls, max(le, e))
        else:
            merged.append((s, e))
    return merged

def invert_intervals(busy: List[Tuple[int, int]], bounds: Tuple[int, int]) -> List[Tuple[int, int]]:
    start, end = bounds
    if not busy:
        return [(start, end)]
    busy = merge_intervals([(max(start, s), min(end, e)) for s, e in busy if e > start and s < end])
    free = []
    cursor = start
    for s, e in busy:
        if cursor < s:
            free.append((cursor, s))
        cursor = max(cursor, e)
    if cursor < end:
        free.append((cursor, end))
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

def split_to_duration(intervals: List[Tuple[int, int]], duration: int) -> List[Tuple[int, int]]:
    slots = []
    for s, e in intervals:
        t = s
        while t + duration <= e:
            slots.append((t, t + duration))
            t += 1  # slide by 1 minute for earliest possible start
    return slots

# Problem setup
work_bounds = (to_minutes("09:00"), to_minutes("17:00"))
duration = 30  # minutes

days = ["Monday", "Tuesday"]

busy: Dict[str, Dict[str, List[Tuple[int, int]]]] = {
    "Shirley": {
        "Monday": [
            (to_minutes("10:30"), to_minutes("11:00")),
            (to_minutes("12:00"), to_minutes("12:30")),
            (to_minutes("16:00"), to_minutes("16:30")),
        ],
        "Tuesday": [
            (to_minutes("09:30"), to_minutes("10:00")),
        ],
    },
    "Albert": {
        "Monday": [
            (to_minutes("09:00"), to_minutes("17:00")),
        ],
        "Tuesday": [
            (to_minutes("09:30"), to_minutes("11:00")),
            (to_minutes("11:30"), to_minutes("12:30")),
            (to_minutes("13:00"), to_minutes("16:00")),
            (to_minutes("16:30"), to_minutes("17:00")),
        ],
    },
}

# Compute common free slots per day
candidates = []
for day in days:
    shirley_free = invert_intervals(busy["Shirley"].get(day, []), work_bounds)
    albert_free = invert_intervals(busy["Albert"].get(day, []), work_bounds)
    common = intersect_intervals(shirley_free, albert_free)
    # Only consider intervals that can fit the duration
    dur_slots = split_to_duration(common, duration)
    for s, e in dur_slots:
        candidates.append((day, s, e))

# Apply preference: Shirley would rather not meet on Tuesday after 10:30
preferred = []
non_preferred = []
tuesday_cutoff = to_minutes("10:30")
for day, s, e in candidates:
    if day == "Tuesday" and s > tuesday_cutoff:
        non_preferred.append((day, s, e))
    else:
        preferred.append((day, s, e))

# Choose the earliest available preferred slot; if none, pick earliest overall
def sort_key(item):
    day, s, e = item
    day_order = days.index(day)
    return (day_order, s, e)

chosen = None
if preferred:
    chosen = min(preferred, key=sort_key)
elif candidates:
    chosen = min(candidates, key=sort_key)
else:
    raise RuntimeError("No viable meeting slots found.")

day, start, end = chosen
print(f"{day} {{{to_hhmm(start)}:{to_hhmm(end)}}}")