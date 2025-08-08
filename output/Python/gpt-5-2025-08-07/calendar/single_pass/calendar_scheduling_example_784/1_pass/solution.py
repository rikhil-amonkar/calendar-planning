from typing import List, Tuple

# Helpers
def to_minutes(hhmm: str) -> int:
    h, m = map(int, hhmm.split(":"))
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

def clamp_intervals(intervals: List[Tuple[int, int]], start: int, end: int) -> List[Tuple[int, int]]:
    clamped = []
    for s, e in intervals:
        s2, e2 = max(s, start), min(e, end)
        if s2 < e2:
            clamped.append((s2, e2))
    return clamped

def complement_within(busy: List[Tuple[int, int]], start: int, end: int) -> List[Tuple[int, int]]:
    busy = merge_intervals(clamp_intervals(busy, start, end))
    free = []
    cur = start
    for s, e in busy:
        if cur < s:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < end:
        free.append((cur, end))
    return free

def intersect_intervals(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    i = j = 0
    result = []
    while i < len(a) and j < len(b):
        s = max(a[i][0], b[j][0])
        e = min(a[i][1], b[j][1])
        if s < e:
            result.append((s, e))
        if a[i][1] < b[j][1]:
            i += 1
        else:
            j += 1
    return result

# Data
WORK_START = to_minutes("09:00")
WORK_END   = to_minutes("17:00")
DURATION   = 60  # minutes

days = ["Monday", "Tuesday", "Wednesday"]

judith_busy = {
    "Monday":    [(to_minutes("12:00"), to_minutes("12:30"))],
    "Tuesday":   [],
    "Wednesday": [(to_minutes("11:30"), to_minutes("12:00"))],
}

timothy_busy = {
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

# Preferences (soft):
# - Avoid Monday if possible
# - Avoid Wednesday before 12:00
NOON = to_minutes("12:00")
def preference_score(day: str, start_min: int) -> int:
    if day == "Tuesday":
        return 0
    if day == "Wednesday" and start_min >= NOON:
        return 1
    if day == "Monday":
        return 2
    if day == "Wednesday" and start_min < NOON:
        return 3
    return 9

# Compute candidates
candidates = []
for day in days:
    j_free = complement_within(judith_busy.get(day, []), WORK_START, WORK_END)
    t_free = complement_within(timothy_busy.get(day, []), WORK_START, WORK_END)
    common = intersect_intervals(j_free, t_free)
    for s, e in common:
        if e - s >= DURATION:
            start = s
            end = s + DURATION
            candidates.append((preference_score(day, start), day, start, end))

# Choose best by preference, then earliest start
if not candidates:
    raise SystemExit("No feasible time found, but a solution was expected.")
candidates.sort()
_, best_day, best_start, best_end = candidates[0]

# Output
print(f"{best_day} {{{to_hhmm(best_start)}:{to_hhmm(best_end)}}}")