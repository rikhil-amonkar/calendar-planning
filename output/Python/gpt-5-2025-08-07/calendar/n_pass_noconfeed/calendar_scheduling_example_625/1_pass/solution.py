from typing import List, Tuple, Dict

# Time helpers
def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

Interval = Tuple[int, int]

def subtract_intervals(base: Interval, blocks: List[Interval]) -> List[Interval]:
    """Return portions of base interval not covered by blocks. Intervals are [start, end) in minutes."""
    start, end = base
    free = []
    current = start
    for b_start, b_end in sorted(blocks):
        if b_end <= current or b_start >= end:
            continue
        if b_start > current:
            free.append((current, min(b_start, end)))
        current = max(current, b_end)
        if current >= end:
            break
    if current < end:
        free.append((current, end))
    return [(s, e) for s, e in free if e > s]

def intersect_intervals(a: List[Interval], b: List[Interval]) -> List[Interval]:
    """Intersect two lists of intervals [start, end)."""
    i, j = 0, 0
    out = []
    a_sorted = sorted(a)
    b_sorted = sorted(b)
    while i < len(a_sorted) and j < len(b_sorted):
        s = max(a_sorted[i][0], b_sorted[j][0])
        e = min(a_sorted[i][1], b_sorted[j][1])
        if s < e:
            out.append((s, e))
        if a_sorted[i][1] < b_sorted[j][1]:
            i += 1
        else:
            j += 1
    return out

# Problem setup
work_hours = ("09:00", "17:00")
meeting_duration_min = 30
days = ["Monday", "Tuesday"]

# Jeffrey is free entire week during work hours
jeffrey_busy: Dict[str, List[Interval]] = {d: [] for d in days}

# Harold's busy times
harold_busy: Dict[str, List[Interval]] = {
    "Monday": [("09:00","10:00"), ("10:30","17:00")],
    "Tuesday": [("09:00","09:30"), ("10:30","11:30"), ("12:30","13:30"), ("14:30","15:30"), ("16:00","17:00")]
}
harold_busy = {d: [(to_minutes(s), to_minutes(e)) for s, e in harold_busy[d]] for d in days}

# Preferences:
# - Avoid Monday if possible
# - Avoid Tuesday before 14:30
avoid_day = "Monday"
tuesday_avoid_before = to_minutes("14:30")

def day_free_intervals(busy: List[Interval]) -> List[Interval]:
    base = (to_minutes(work_hours[0]), to_minutes(work_hours[1]))
    return subtract_intervals(base, busy)

# Compute common free intervals per day
common_free: Dict[str, List[Interval]] = {}
for d in days:
    jeff_free = day_free_intervals(jeffrey_busy[d])
    har_free = day_free_intervals(harold_busy[d])
    common_free[d] = intersect_intervals(jeff_free, har_free)

# Generate candidate start times respecting duration
candidates: List[Tuple[str, int, int]] = []  # (day, start, end)
for d in days:
    for s, e in common_free[d]:
        if e - s >= meeting_duration_min:
            # Primary candidate: start at interval start
            candidates.append((d, s, s + meeting_duration_min))
            # If Tuesday and interval spans past the preference threshold, consider a start at/after 14:30
            if d == "Tuesday":
                pref_start = max(s, tuesday_avoid_before)
                if pref_start + meeting_duration_min <= e and pref_start != s:
                    candidates.append((d, pref_start, pref_start + meeting_duration_min))

# Rank candidates by preferences
def preference_score(day: str, start: int) -> Tuple[int, int]:
    score = 0
    # Strongly prefer not Monday
    if day == avoid_day:
        score += 10
    # On Tuesday, prefer times at or after 14:30
    if day == "Tuesday" and start < tuesday_avoid_before:
        score += 1
    # Secondary tie-breakers: earlier day in list after preferences, then earlier time
    day_order = days.index(day)
    return (score, day_order)

best = None
best_key = None
for d, s, e in candidates:
    key = (*preference_score(d, s), s, e)
    if best is None or key < best_key:
        best = (d, s, e)
        best_key = key

if not best:
    raise RuntimeError("No feasible meeting time found, but a solution was expected.")

chosen_day, chosen_start, chosen_end = best

# Output both the time range and the day of the week
print(chosen_day)
print(f"{{{to_hhmm(chosen_start)}:{to_hhmm(chosen_end)}}}")