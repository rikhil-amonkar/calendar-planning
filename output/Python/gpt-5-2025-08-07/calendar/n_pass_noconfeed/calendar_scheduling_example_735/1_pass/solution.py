from typing import List, Tuple, Dict

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

def clip_intervals(intervals: List[Tuple[int, int]], start: int, end: int) -> List[Tuple[int, int]]:
    clipped = []
    for s, e in intervals:
        s2, e2 = max(s, start), min(e, end)
        if s2 < e2:
            clipped.append((s2, e2))
    return clipped

def invert_intervals(busy: List[Tuple[int, int]], start: int, end: int) -> List[Tuple[int, int]]:
    if not busy:
        return [(start, end)]
    busy = merge_intervals(clip_intervals(busy, start, end))
    free = []
    cur = start
    for s, e in busy:
        if cur < s:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < end:
        free.append((cur, end))
    return free

def intersect_two(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
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
work_start, work_end = to_minutes("09:00"), to_minutes("17:00")
duration = 30  # minutes
days = ["Monday", "Tuesday", "Wednesday"]

schedules: Dict[str, Dict[str, List[Tuple[str, str]]]] = {
    "Ronald": {
        "Monday": [("10:30","11:00"), ("12:00","12:30"), ("15:30","16:00")],
        "Tuesday": [("09:00","09:30"), ("12:00","12:30"), ("15:30","16:30")],
        "Wednesday": [("09:30","10:30"), ("11:00","12:00"), ("12:30","13:00"), ("13:30","14:00"), ("16:30","17:00")],
    },
    "Amber": {
        "Monday": [("09:00","09:30"), ("10:00","10:30"), ("11:30","12:00"), ("12:30","14:00"), ("14:30","15:00"), ("15:30","17:00")],
        "Tuesday": [("09:00","09:30"), ("10:00","11:30"), ("12:00","12:30"), ("13:30","15:30"), ("16:30","17:00")],
        "Wednesday": [("09:00","09:30"), ("10:00","10:30"), ("11:00","13:30"), ("15:00","15:30")],
    }
}

# Convert schedules to minutes
schedules_min: Dict[str, Dict[str, List[Tuple[int, int]]]] = {}
for person, per_day in schedules.items():
    schedules_min[person] = {}
    for day, intervals in per_day.items():
        schedules_min[person][day] = [(to_minutes(s), to_minutes(e)) for s, e in intervals]

def find_earliest_slot() -> Tuple[str, Tuple[int, int]]:
    for day in days:
        # Compute free intervals per participant
        free_lists = []
        for person in schedules_min:
            busy = schedules_min[person].get(day, [])
            free = invert_intervals(busy, work_start, work_end)
            free_lists.append(free)
        # Intersect all participants' free intervals
        common = free_lists[0]
        for fl in free_lists[1:]:
            common = intersect_two(common, fl)
            if not common:
                break
        # Find earliest interval of at least 'duration'
        for s, e in common:
            if e - s >= duration:
                return day, (s, s + duration)
    raise ValueError("No suitable slot found")

day, (start, end) = find_earliest_slot()
print(day)
print("{" + f"{to_hhmm(start)}:{to_hhmm(end)}" + "}")