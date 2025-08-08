from typing import List, Tuple, Dict

# Helper functions
def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_time_str(m: int) -> str:
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

def clamp_interval(interval: Tuple[int, int], bounds: Tuple[int, int]) -> Tuple[int, int] | None:
    s, e = interval
    bs, be = bounds
    s2, e2 = max(s, bs), min(e, be)
    if s2 < e2:
        return (s2, e2)
    return None

def complement_within(bounds: Tuple[int, int], busy: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    # Clamp busy intervals to bounds and merge
    clamped = []
    for iv in busy:
        c = clamp_interval(iv, bounds)
        if c:
            clamped.append(c)
    merged = merge_intervals(clamped)
    free = []
    cur = bounds[0]
    for s, e in merged:
        if cur < s:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < bounds[1]:
        free.append((cur, bounds[1]))
    return free

def intersect_intervals(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    i, j = 0, 0
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

def earliest_slot(intervals: List[Tuple[int, int]], duration: int) -> Tuple[int, int] | None:
    for s, e in intervals:
        if e - s >= duration:
            return (s, s + duration)
    return None

# Data setup based on the task
work_hours = (to_minutes("09:00"), to_minutes("17:00"))
meeting_duration = 30  # minutes
days_order = ["Monday", "Tuesday", "Wednesday"]

arthur_busy: Dict[str, List[Tuple[int, int]]] = {
    "Monday": [(to_minutes("11:00"), to_minutes("11:30")),
               (to_minutes("13:30"), to_minutes("14:00")),
               (to_minutes("15:00"), to_minutes("15:30"))],
    "Tuesday": [(to_minutes("13:00"), to_minutes("13:30")),
                (to_minutes("16:00"), to_minutes("16:30"))],
    "Wednesday": [(to_minutes("10:00"), to_minutes("10:30")),
                  (to_minutes("11:00"), to_minutes("11:30")),
                  (to_minutes("12:00"), to_minutes("12:30")),
                  (to_minutes("14:00"), to_minutes("14:30")),
                  (to_minutes("16:00"), to_minutes("16:30"))],
}

michael_busy: Dict[str, List[Tuple[int, int]]] = {
    "Monday": [(to_minutes("09:00"), to_minutes("12:00")),
               (to_minutes("12:30"), to_minutes("13:00")),
               (to_minutes("14:00"), to_minutes("14:30")),
               (to_minutes("15:00"), to_minutes("17:00"))],
    "Tuesday": [(to_minutes("09:30"), to_minutes("11:30")),
                (to_minutes("12:00"), to_minutes("13:30")),
                (to_minutes("14:00"), to_minutes("15:30"))],
    "Wednesday": [(to_minutes("10:00"), to_minutes("12:30")),
                  (to_minutes("13:00"), to_minutes("13:30"))],
}

# Constraint: Arthur cannot meet on Tuesday
disallowed_days_for_arthur = {"Tuesday"}

# Compute earliest meeting
result = None

for day in days_order:
    if day in disallowed_days_for_arthur:
        continue
    arthur_free = complement_within(work_hours, arthur_busy.get(day, []))
    michael_free = complement_within(work_hours, michael_busy.get(day, []))
    common_free = intersect_intervals(arthur_free, michael_free)
    slot = earliest_slot(common_free, meeting_duration)
    if slot:
        result = (day, slot[0], slot[1])
        break

if not result:
    raise SystemExit("No feasible meeting time found, but the task guarantees a solution.")

day, start_m, end_m = result
start_str = to_time_str(start_m)
end_str = to_time_str(end_m)

# Output: day and time range like {HH:MM:HH:MM}
print(day)
print(f"{{{start_str}:{end_str}}}")