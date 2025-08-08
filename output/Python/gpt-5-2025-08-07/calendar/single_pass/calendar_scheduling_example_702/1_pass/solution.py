from typing import List, Tuple, Dict

# Helpers for time conversion
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

def complement_within(bounds: Tuple[int, int], busy: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    start, end = bounds
    if not busy:
        return [(start, end)]
    free = []
    cur = start
    for s, e in busy:
        s = max(s, start)
        e = min(e, end)
        if e <= start or s >= end:
            continue
        if s > cur:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < end:
        free.append((cur, end))
    # Filter any zero/negative durations
    return [(s, e) for s, e in free if e - s > 0]

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

# Input data per the task
work_start, work_end = to_minutes("09:00"), to_minutes("17:00")
work_bounds = (work_start, work_end)
meeting_duration = 30  # minutes

days = ["Monday", "Tuesday", "Wednesday"]

schedules: Dict[str, Dict[str, List[Tuple[str, str]]]] = {
    "Robert": {
        "Monday":    [("11:00", "11:30"), ("14:00", "14:30"), ("15:30", "16:00")],
        "Tuesday":   [("10:30", "11:00"), ("15:00", "15:30")],
        "Wednesday": [("10:00", "11:00"), ("11:30", "12:00"), ("12:30", "13:00"),
                      ("13:30", "14:00"), ("15:00", "15:30"), ("16:00", "16:30")],
    },
    "Ralph": {
        "Monday":    [("10:00", "13:30"), ("14:00", "14:30"), ("15:00", "17:00")],
        "Tuesday":   [("09:00", "09:30"), ("10:00", "10:30"), ("11:00", "11:30"),
                      ("12:00", "13:00"), ("14:00", "15:30"), ("16:00", "17:00")],
        "Wednesday": [("10:30", "11:00"), ("11:30", "12:00"), ("13:00", "14:30"),
                      ("16:30", "17:00")],
    },
}

# Preference: avoid Monday if possible, choose earliest availability otherwise
avoid_day = "Monday"
preferred_day_order = [d for d in days if d != avoid_day] + [avoid_day]

# Preprocess schedules into busy intervals in minutes (merged and clipped to work hours)
busy_minutes: Dict[str, Dict[str, List[Tuple[int, int]]]] = {p: {} for p in schedules}
for person, day_map in schedules.items():
    for day in days:
        raw = [(to_minutes(s), to_minutes(e)) for s, e in day_map.get(day, [])]
        # Clip to work hours and remove out-of-bounds
        clipped = []
        for s, e in raw:
            if e <= work_start or s >= work_end:
                continue
            clipped.append((max(s, work_start), min(e, work_end)))
        busy_minutes[person][day] = merge_intervals(clipped)

# Find earliest slot respecting preference
found = None  # (day, start, end)
for day in preferred_day_order:
    # Compute each participant's free intervals
    free_lists = []
    for person in schedules.keys():
        busy = busy_minutes[person][day]
        free = complement_within(work_bounds, busy)
        free_lists.append(free)

    # Intersect free intervals across all participants
    if not free_lists:
        continue
    common = free_lists[0]
    for fl in free_lists[1:]:
        common = intersect_intervals(common, fl)
        if not common:
            break

    # Within common intervals, find the earliest slot of required duration
    for s, e in common:
        if e - s >= meeting_duration:
            start = s
            end = s + meeting_duration
            found = (day, start, end)
            break
    if found:
        break

# Output result
if not found:
    raise SystemExit("No feasible time found, but problem statement guarantees a solution.")

day, start, end = found
print(f"{day} {to_hhmm(start)}:{to_hhmm(end)}")