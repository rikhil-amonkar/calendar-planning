from typing import List, Tuple, Dict

# Helper functions
def t2m(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def m2t(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

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

def invert_within(bounds: Tuple[int, int], busy: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    start, end = bounds
    busy = merge_intervals([(max(start, s), min(end, e)) for s, e in busy if e > start and s < end])
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

def slots_of_duration(intervals: List[Tuple[int, int]], dur: int) -> List[Tuple[int, int]]:
    return [(s, s + dur) for s, e in intervals if e - s >= dur]

# Problem setup (from the task)
work_hours = (t2m("09:00"), t2m("17:00"))
meeting_days = ["Monday", "Tuesday", "Wednesday"]
duration = 30  # minutes

# Busy schedules
tyler_busy: Dict[str, List[Tuple[int, int]]] = {
    "Monday": [],
    "Tuesday": [(t2m("09:00"), t2m("09:30")), (t2m("14:30"), t2m("15:00"))],
    "Wednesday": [
        (t2m("10:30"), t2m("11:00")),
        (t2m("12:30"), t2m("13:00")),
        (t2m("13:30"), t2m("14:00")),
        (t2m("16:30"), t2m("17:00")),
    ],
}
ruth_busy: Dict[str, List[Tuple[int, int]]] = {
    "Monday": [
        (t2m("09:00"), t2m("10:00")),
        (t2m("10:30"), t2m("12:00")),
        (t2m("12:30"), t2m("14:30")),
        (t2m("15:00"), t2m("16:00")),
        (t2m("16:30"), t2m("17:00")),
    ],
    "Tuesday": [(t2m("09:00"), t2m("17:00"))],
    "Wednesday": [(t2m("09:00"), t2m("17:00"))],
}

# Preference: Tyler would like to avoid more meetings on Monday before 16:00.
# Implement as an additional "busy" block for Tyler on Monday from 09:00 to 16:00.
tyler_preference_blocks: Dict[str, List[Tuple[int, int]]] = {
    "Monday": [(t2m("09:00"), t2m("16:00"))]
}

# Build availability per day for each participant
def availability_for_day(busy_map: Dict[str, List[Tuple[int, int]]], day: str) -> List[Tuple[int, int]]:
    return invert_within(work_hours, busy_map.get(day, []))

# Apply preferences by treating them as additional busy times (hard preference)
def apply_preferences(busy_map: Dict[str, List[Tuple[int, int]]],
                      prefs: Dict[str, List[Tuple[int, int]]]) -> Dict[str, List[Tuple[int, int]]]:
    out = {}
    for d in meeting_days:
        out[d] = merge_intervals(busy_map.get(d, []) + prefs.get(d, []))
    return out

tyler_busy_with_prefs = apply_preferences(tyler_busy, tyler_preference_blocks)

# Find the earliest feasible slot by day order then time
proposal = None
for day in meeting_days:
    tyler_free = availability_for_day(tyler_busy_with_prefs, day)
    ruth_free = availability_for_day(ruth_busy, day)
    common = intersect_intervals(tyler_free, ruth_free)
    candidates = slots_of_duration(common, duration)
    if candidates:
        start, end = candidates[0]
        proposal = (day, start, end)
        break

# Output result
if proposal:
    day, s, e = proposal
    time_range = f"{m2t(s)}:{m2t(e)}"
    print(day)
    print("{" + time_range + "}")
else:
    print("No feasible time found")