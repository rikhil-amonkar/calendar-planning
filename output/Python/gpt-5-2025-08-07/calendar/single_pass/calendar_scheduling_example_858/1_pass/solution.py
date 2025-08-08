from typing import List, Tuple

# Helper functions
def to_minutes(h: int, m: int) -> int:
    return h * 60 + m

def to_hhmm(t: int) -> str:
    return f"{t//60:02d}:{t%60:02d}"

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

def invert_intervals(busy: List[Tuple[int, int]], start: int, end: int) -> List[Tuple[int, int]]:
    free = []
    cursor = start
    for s, e in busy:
        if s > cursor:
            free.append((cursor, s))
        cursor = max(cursor, e)
    if cursor < end:
        free.append((cursor, end))
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

# Work hours and days
WORK_START = to_minutes(9, 0)
WORK_END = to_minutes(17, 0)
days = ["Monday", "Tuesday", "Wednesday", "Thursday"]

# Schedules (busy times)
carl_busy = {
    "Monday":    [(to_minutes(11,0),  to_minutes(11,30))],
    "Tuesday":   [(to_minutes(14,30), to_minutes(15,0))],
    "Wednesday": [(to_minutes(10,0),  to_minutes(11,30)),
                  (to_minutes(13,0),  to_minutes(13,30))],
    "Thursday":  [(to_minutes(13,30), to_minutes(14,0)),
                  (to_minutes(16,0),  to_minutes(16,30))],
}

margaret_busy = {
    "Monday":    [(to_minutes(9,0),   to_minutes(10,30)),
                  (to_minutes(11,0),  to_minutes(17,0))],
    "Tuesday":   [(to_minutes(9,30),  to_minutes(12,0)),
                  (to_minutes(13,30), to_minutes(14,0)),
                  (to_minutes(15,30), to_minutes(17,0))],
    "Wednesday": [(to_minutes(9,30),  to_minutes(12,0)),
                  (to_minutes(12,30), to_minutes(13,0)),
                  (to_minutes(13,30), to_minutes(14,30)),
                  (to_minutes(15,0),  to_minutes(17,0))],
    "Thursday":  [(to_minutes(10,0),  to_minutes(12,0)),
                  (to_minutes(12,30), to_minutes(14,0)),
                  (to_minutes(14,30), to_minutes(17,0))],
}

# Clamp to work hours and merge
def prepare_busy(day: str, person_busy: dict) -> List[Tuple[int, int]]:
    intervals = []
    for s, e in person_busy.get(day, []):
        s_clamped = max(s, WORK_START)
        e_clamped = min(e, WORK_END)
        if s_clamped < e_clamped:
            intervals.append((s_clamped, e_clamped))
    return merge_intervals(intervals)

# Find all candidate 60-min slots across days
MEETING_DURATION = 60  # minutes

candidates = []
for d_idx, day in enumerate(days):
    carl_day_busy = prepare_busy(day, carl_busy)
    marg_day_busy = prepare_busy(day, margaret_busy)
    carl_free = invert_intervals(carl_day_busy, WORK_START, WORK_END)
    marg_free = invert_intervals(marg_day_busy, WORK_START, WORK_END)
    overlap = intersect_intervals(carl_free, marg_free)
    for s, e in overlap:
        if e - s >= MEETING_DURATION:
            # Earliest 60-min window within this overlap
            start = s
            end = s + MEETING_DURATION
            candidates.append((day, d_idx, start, end))

# Preference: avoid Thursday if possible
# Priority: non-Thursday first, then by day order (Mon->Thu), then by earliest time
def priority(day: str) -> int:
    return 1 if day == "Thursday" else 0

candidates.sort(key=lambda x: (priority(x[0]), x[1], x[2]))

if not candidates:
    raise SystemExit("No feasible meeting slot found.")

day, _, start, end = candidates[0]
time_range = f"{to_hhmm(start)}:{to_hhmm(end)}"

# Output: day and time range in required format
print(day)
print(f"{{{time_range}}}")