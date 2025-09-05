from typing import List, Tuple, Dict

# Helpers
def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m//60:02d}:{m%60:02d}"

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

def complement_intervals(busy: List[Tuple[int, int]], day_start: int, day_end: int) -> List[Tuple[int, int]]:
    free = []
    current = day_start
    for s, e in busy:
        s = max(s, day_start)
        e = min(e, day_end)
        if e <= day_start or s >= day_end:
            continue
        if s > current:
            free.append((current, s))
        current = max(current, e)
    if current < day_end:
        free.append((current, day_end))
    return free

def intersect_intervals(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
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

# Data
work_start, work_end = to_minutes("09:00"), to_minutes("17:00")
meeting_duration = 30  # minutes

days = ["Monday", "Tuesday", "Wednesday"]

amy_busy: Dict[str, List[Tuple[int, int]]] = {
    "Monday": [],
    "Tuesday": [],
    "Wednesday": [(to_minutes("11:00"), to_minutes("11:30")),
                  (to_minutes("13:30"), to_minutes("14:00"))],
}

pamela_busy: Dict[str, List[Tuple[int, int]]] = {
    "Monday": [(to_minutes("09:00"), to_minutes("10:30")),
               (to_minutes("11:00"), to_minutes("16:30"))],
    "Tuesday": [(to_minutes("09:00"), to_minutes("09:30")),
                (to_minutes("10:00"), to_minutes("17:00"))],
    "Wednesday": [(to_minutes("09:00"), to_minutes("09:30")),
                  (to_minutes("10:00"), to_minutes("11:00")),
                  (to_minutes("11:30"), to_minutes("13:30")),
                  (to_minutes("14:30"), to_minutes("15:00")),
                  (to_minutes("16:00"), to_minutes("16:30"))],
}

# Preferences:
# - Pamela would like to avoid meetings on Monday and Tuesday.
# - On Wednesday, avoid times before 16:00 if possible.
def preference_score(day: str, start_min: int) -> Tuple[int, int, int]:
    # Lower tuple is better.
    if day == "Wednesday" and start_min >= to_minutes("16:00"):
        return (0, start_min, 0)  # Best: Wednesday after 16:00
    if day == "Wednesday":
        return (1, start_min, 0)  # Next: Wednesday before 16:00
    if day in ("Monday", "Tuesday"):
        return (2, start_min, 0)  # Least preferred: Monday or Tuesday
    return (3, start_min, 0)      # Fallback (not expected)

# Compute common free slots and select best based on preferences
candidates = []  # (day, start_min)

for day in days:
    # Merge busy intervals and compute free windows for each participant
    amy_free = complement_intervals(merge_intervals(amy_busy[day]), work_start, work_end)
    pamela_free = complement_intervals(merge_intervals(pamela_busy[day]), work_start, work_end)
    common_free = intersect_intervals(amy_free, pamela_free)

    for s, e in common_free:
        if e - s >= meeting_duration:
            candidates.append((day, s))

# Choose the best candidate according to preference score, tie-break by earliest time
best = min(candidates, key=lambda x: preference_score(x[0], x[1]))

best_day, best_start = best
best_end = best_start + meeting_duration

# Output
print(best_day)
print(f"{{{to_hhmm(best_start)}:{to_hhmm(best_end)}}}")