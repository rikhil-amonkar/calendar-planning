from typing import List, Tuple, Dict

# Utilities
def to_min(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_str(m: int) -> str:
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

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

def invert_intervals(busy: List[Tuple[int, int]], bounds: Tuple[int, int]) -> List[Tuple[int, int]]:
    start, end = bounds
    if not busy:
        return [(start, end)]
    busy = merge_intervals(busy)
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
        s1, e1 = a[i]
        s2, e2 = b[j]
        s, e = max(s1, s2), min(e1, e2)
        if s < e:
            res.append((s, e))
        if e1 < e2:
            i += 1
        else:
            j += 1
    return res

def first_slot_of_duration(intervals: List[Tuple[int, int]], duration: int) -> Tuple[int, int] | None:
    for s, e in intervals:
        if e - s >= duration:
            return (s, s + duration)
    return None

# Data
WORK_HOURS = (to_min("09:00"), to_min("17:00"))
MEETING_DURATION = 30  # minutes

busy: Dict[str, Dict[str, List[Tuple[int, int]]]] = {
    "Jesse": {
        "Monday": [(to_min("13:30"), to_min("14:00")), (to_min("14:30"), to_min("15:00"))],
        "Tuesday": [(to_min("09:00"), to_min("09:30")),
                    (to_min("13:00"), to_min("13:30")),
                    (to_min("14:00"), to_min("15:00"))],
    },
    "Lawrence": {
        "Monday": [(to_min("09:00"), to_min("17:00"))],
        "Tuesday": [(to_min("09:30"), to_min("10:30")),
                    (to_min("11:30"), to_min("12:30")),
                    (to_min("13:00"), to_min("13:30")),
                    (to_min("14:30"), to_min("15:00")),
                    (to_min("15:30"), to_min("16:30"))],
    },
}

days_order = ["Monday", "Tuesday"]

# Additional constraint: Lawrence cannot meet on Tuesday after 16:30 (meeting must end by 16:30)
tuesday_end_cap = to_min("16:30")

def day_bounds(day: str) -> Tuple[int, int]:
    if day == "Tuesday":
        # Meeting must end by 16:30, so cap the work hours end at 16:30
        return (WORK_HOURS[0], min(WORK_HOURS[1], tuesday_end_cap))
    return WORK_HOURS

# Compute
for day in days_order:
    bounds = day_bounds(day)
    # Free intervals for each participant within bounds
    free_all = []
    for person in ["Jesse", "Lawrence"]:
        person_busy = busy.get(person, {}).get(day, [])
        # Clip busy intervals to bounds
        clipped_busy = []
        for s, e in person_busy:
            if e <= bounds[0] or s >= bounds[1]:
                continue
            clipped_busy.append((max(s, bounds[0]), min(e, bounds[1])))
        free = invert_intervals(clipped_busy, bounds)
        free_all.append(free)

    # Intersect all participants' free intervals
    common_free = free_all[0]
    for f in free_all[1:]:
        common_free = intersect_intervals(common_free, f)

    slot = first_slot_of_duration(common_free, MEETING_DURATION)
    if slot:
        start, end = slot
        time_range = f"{{{to_str(start)}:{to_str(end)}}}"
        print(f"{day} {time_range}")
        break