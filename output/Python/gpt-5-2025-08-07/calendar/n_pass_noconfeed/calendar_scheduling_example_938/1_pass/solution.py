from typing import List, Tuple, Dict

# Helper functions
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
    for start, end in intervals[1:]:
        last_start, last_end = merged[-1]
        if start <= last_end:
            merged[-1] = (last_start, max(last_end, end))
        else:
            merged.append((start, end))
    return merged

def invert_intervals(busy: List[Tuple[int, int]], work_start: int, work_end: int) -> List[Tuple[int, int]]:
    if not busy:
        return [(work_start, work_end)]
    busy = merge_intervals([(max(work_start, s), min(work_end, e)) for s, e in busy if e > work_start and s < work_end])
    free = []
    cursor = work_start
    for s, e in busy:
        if cursor < s:
            free.append((cursor, s))
        cursor = max(cursor, e)
    if cursor < work_end:
        free.append((cursor, work_end))
    return free

def intersect(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
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

# Inputs
work_hours = ("09:00", "17:00")
meeting_duration_min = 30

days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
# Preference: avoid Wednesday if possible
day_preference = ["Monday", "Tuesday", "Thursday", "Friday", "Wednesday"]

eugene_busy_str: Dict[str, List[Tuple[str, str]]] = {
    "Monday":    [("11:00","12:00"), ("13:30","14:00"), ("14:30","15:00"), ("16:00","16:30")],
    "Tuesday":   [],
    "Wednesday": [("09:00","09:30"), ("11:00","11:30"), ("12:00","12:30"), ("13:30","15:00")],
    "Thursday":  [("09:30","10:00"), ("11:00","12:30")],
    "Friday":    [("10:30","11:00"), ("12:00","12:30"), ("13:00","13:30")],
}

eric_busy_str: Dict[str, List[Tuple[str, str]]] = {
    "Monday":    [("09:00","17:00")],
    "Tuesday":   [("09:00","17:00")],
    "Wednesday": [("09:00","11:30"), ("12:00","14:00"), ("14:30","16:30")],
    "Thursday":  [("09:00","17:00")],
    "Friday":    [("09:00","11:00"), ("11:30","17:00")],
}

# Convert times to minutes
ws, we = map(to_minutes, work_hours)
eugene_busy = {d: [(to_minutes(s), to_minutes(e)) for s, e in eugene_busy_str.get(d, [])] for d in days}
eric_busy   = {d: [(to_minutes(s), to_minutes(e)) for s, e in eric_busy_str.get(d, [])] for d in days}

# Search for earliest feasible slot honoring preference (avoid Wednesday)
chosen_day = None
chosen_slot = None

for day in day_preference:
    e_free = invert_intervals(eugene_busy.get(day, []), ws, we)
    r_free = invert_intervals(eric_busy.get(day, []), ws, we)
    common = intersect(e_free, r_free)
    # Find earliest slot of required duration
    for s, e in common:
        if e - s >= meeting_duration_min:
            chosen_day = day
            chosen_slot = (s, s + meeting_duration_min)
            break
    if chosen_slot:
        break

# Output
if not chosen_slot:
    raise SystemExit("No feasible slot found (unexpected based on problem statement).")

start_str = to_hhmm(chosen_slot[0])
end_str = to_hhmm(chosen_slot[1])

# Print both day and the time range in the requested format
print(chosen_day)
print(f"{{{start_str}:{end_str}}}")