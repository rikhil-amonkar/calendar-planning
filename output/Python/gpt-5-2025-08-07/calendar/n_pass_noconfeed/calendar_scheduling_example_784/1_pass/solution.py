from typing import List, Tuple, Dict

# Helper functions
def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_time(m: int) -> str:
    return f"{m//60:02d}:{m%60:02d}"

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

def complement_within(work: Tuple[int, int], busy: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    ws, we = work
    busy_merged = merge_intervals([(max(ws, s), min(we, e)) for s, e in busy if e > ws and s < we])
    free = []
    cur = ws
    for s, e in busy_merged:
        if cur < s:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < we:
        free.append((cur, we))
    return free

def intersect_intervals(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    i, j = 0, 0
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

# Problem setup
work_hours: Dict[str, Tuple[int, int]] = {
    "Monday": (to_minutes("09:00"), to_minutes("17:00")),
    "Tuesday": (to_minutes("09:00"), to_minutes("17:00")),
    "Wednesday": (to_minutes("09:00"), to_minutes("17:00")),
}

judith_busy: Dict[str, List[Tuple[int, int]]] = {
    "Monday": [(to_minutes("12:00"), to_minutes("12:30"))],
    "Tuesday": [],
    "Wednesday": [(to_minutes("11:30"), to_minutes("12:00"))],
}

timothy_busy: Dict[str, List[Tuple[int, int]]] = {
    "Monday": [
        (to_minutes("09:30"), to_minutes("10:00")),
        (to_minutes("10:30"), to_minutes("11:30")),
        (to_minutes("12:30"), to_minutes("14:00")),
        (to_minutes("15:30"), to_minutes("17:00")),
    ],
    "Tuesday": [
        (to_minutes("09:30"), to_minutes("13:00")),
        (to_minutes("13:30"), to_minutes("14:00")),
        (to_minutes("14:30"), to_minutes("17:00")),
    ],
    "Wednesday": [
        (to_minutes("09:00"), to_minutes("09:30")),
        (to_minutes("10:30"), to_minutes("11:00")),
        (to_minutes("13:30"), to_minutes("14:30")),
        (to_minutes("15:00"), to_minutes("15:30")),
        (to_minutes("16:00"), to_minutes("16:30")),
    ],
}

duration = 60  # minutes

# Preferences (lower is better)
def preference_penalty(day: str, start: int) -> int:
    penalty = 0
    # Judith would like to avoid more meetings on Monday
    if day == "Monday":
        penalty += 2
    # Judith would like to avoid Wednesday before 12:00
    if day == "Wednesday" and start < to_minutes("12:00"):
        penalty += 1
    return penalty

# Generate candidates
candidates = []  # (penalty, day_order, start_time, end_time, day)
day_order_map = {"Monday": 0, "Tuesday": 1, "Wednesday": 2}

for day in ["Monday", "Tuesday", "Wednesday"]:
    ws, we = work_hours[day]
    judith_free = complement_within((ws, we), judith_busy[day])
    timothy_free = complement_within((ws, we), timothy_busy[day])
    common_free = intersect_intervals(judith_free, timothy_free)
    for s, e in common_free:
        if e - s >= duration:
            start = s
            end = s + duration
            penalty = preference_penalty(day, start)
            candidates.append((penalty, day_order_map[day], start, end, day))

# Choose best candidate by preference, then day order, then earliest time
if not candidates:
    raise SystemExit("No available time found.")
candidates.sort()
best = candidates[0]
_, _, start, end, day = best

# Output in required format: include both day of week and time range {HH:MM:HH:MM}
print(f"{day} {{{to_time(start)}:{to_time(end)}}}")