from typing import List, Tuple, Dict

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
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

def free_from_busy(busy: List[Tuple[int, int]], work: Tuple[int, int]) -> List[Tuple[int, int]]:
    ws, we = work
    # Clip busy intervals to work window and merge
    clipped = []
    for s, e in busy:
        s = max(s, ws)
        e = min(e, we)
        if s < e:
            clipped.append((s, e))
    merged = merge_intervals(clipped)
    # Invert to get free intervals
    free = []
    cursor = ws
    for s, e in merged:
        if cursor < s:
            free.append((cursor, s))
        cursor = max(cursor, e)
    if cursor < we:
        free.append((cursor, we))
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

# Inputs
work_hours = {
    "Monday": (to_minutes("09:00"), to_minutes("17:00")),
    "Tuesday": (to_minutes("09:00"), to_minutes("17:00")),
}

busy: Dict[str, Dict[str, List[Tuple[int, int]]]] = {
    "Jean": {
        "Monday": [],
        "Tuesday": [(to_minutes("11:30"), to_minutes("12:00")),
                    (to_minutes("16:00"), to_minutes("16:30"))],
    },
    "Doris": {
        "Monday": [(to_minutes("09:00"), to_minutes("11:30")),
                   (to_minutes("12:00"), to_minutes("12:30")),
                   (to_minutes("13:30"), to_minutes("16:00")),
                   (to_minutes("16:30"), to_minutes("17:00"))],
        "Tuesday": [(to_minutes("09:00"), to_minutes("17:00"))],
    },
}

duration = 30  # minutes
days_order = ["Monday", "Tuesday"]

# Preferences: Doris would rather not meet on Monday after 14:00
preference_cutoff = to_minutes("14:00")

candidates = []

for day_idx, day in enumerate(days_order):
    # Compute free intervals for each participant
    day_work = work_hours[day]
    jean_free = free_from_busy(busy["Jean"][day], day_work)
    doris_free = free_from_busy(busy["Doris"][day], day_work)
    # Common free intervals
    common = intersect(jean_free, doris_free)
    # Generate candidate slots (pick earliest start in each interval if it fits)
    for s, e in common:
        if e - s >= duration:
            start = s
            end = s + duration
            penalty = 0
            if day == "Monday" and start >= preference_cutoff:
                penalty = 1  # less preferred
            # Store as (penalty, day_idx, start, end, day)
            candidates.append((penalty, day_idx, start, end, day))

# Choose best candidate: lowest penalty, then earliest day, then earliest time
candidates.sort()
best = candidates[0]
_, _, start, end, day = best

# Output: day and HH:MM:HH:MM
print(day)
print(f"{to_hhmm(start)}:{to_hhmm(end)}")