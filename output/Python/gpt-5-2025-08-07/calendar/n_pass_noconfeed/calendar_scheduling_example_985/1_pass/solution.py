from typing import List, Tuple, Dict

# Helper functions
def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_str(m: int) -> str:
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

def subtract_from_range(busy: List[Tuple[int, int]], start: int, end: int) -> List[Tuple[int, int]]:
    free = []
    cur = start
    for s, e in busy:
        if s > cur:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < end:
        free.append((cur, end))
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

# Data setup
days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
work_start, work_end = to_minutes("09:00"), to_minutes("17:00")
duration = 60  # minutes

schedules: Dict[str, Dict[str, List[Tuple[str, str]]]] = {
    "Diane": {
        "Monday":    [("12:00", "12:30"), ("15:00", "15:30")],
        "Tuesday":   [("10:00", "11:00"), ("11:30", "12:00"), ("12:30", "13:00"), ("16:00", "17:00")],
        "Wednesday": [("09:00", "09:30"), ("14:30", "15:00"), ("16:30", "17:00")],
        "Thursday":  [("15:30", "16:30")],
        "Friday":    [("09:30", "11:30"), ("14:30", "15:00"), ("16:00", "17:00")],
    },
    "Matthew": {
        "Monday":    [("09:00", "10:00"), ("10:30", "17:00")],
        "Tuesday":   [("09:00", "17:00")],
        "Wednesday": [("09:00", "11:00"), ("12:00", "14:30"), ("16:00", "17:00")],
        "Thursday":  [("09:00", "16:00")],
        "Friday":    [("09:00", "17:00")],
    },
}

# Preference: Matthew would rather not meet on Wednesday before 12:30
preferences_min_start = {"Wednesday": to_minutes("12:30")}

# Compute group availability per day
group_free: Dict[str, List[Tuple[int, int]]] = {}

for day in days:
    # For each participant, compute free intervals within work hours
    participants_free = []
    for person, person_sched in schedules.items():
        busy_raw = person_sched.get(day, [])
        # Convert to minutes and clip to work hours
        busy = []
        for s, e in busy_raw:
            sm, em = to_minutes(s), to_minutes(e)
            if em <= work_start or sm >= work_end:
                continue
            busy.append((max(sm, work_start), min(em, work_end)))
        # Merge overlaps and compute free
        busy_merged = merge_intervals(busy)
        free = subtract_from_range(busy_merged, work_start, work_end)
        participants_free.append(free)

    # Intersect all participants' free intervals to get group free intervals
    if participants_free:
        common = participants_free[0]
        for free in participants_free[1:]:
            common = intersect_intervals(common, free)
        group_free[day] = common
    else:
        group_free[day] = []

# Apply preferences (soft): try to find a slot respecting preferences first
def find_slot(respect_preferences: bool) -> Tuple[str, int, int]:
    for day in days:
        intervals = group_free.get(day, [])
        for s, e in intervals:
            start = s
            # Apply minimum start preference if requested
            if respect_preferences and day in preferences_min_start:
                start = max(start, preferences_min_start[day])
            if e - start >= duration:
                return day, start, start + duration
    return "", -1, -1

day, start, end = find_slot(respect_preferences=True)
if day == "":
    # Fallback ignoring preferences (shouldn't be needed for this case)
    day, start, end = find_slot(respect_preferences=False)

# Output
print(f"{day} {{{to_str(start)}:{to_str(end)}}}")