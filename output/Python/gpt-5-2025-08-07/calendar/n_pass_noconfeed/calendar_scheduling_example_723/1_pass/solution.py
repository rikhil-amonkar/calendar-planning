# Meeting Scheduler for Arthur and Michael
# Finds the earliest 30-minute meeting between 09:00 and 17:00 on Mon-Wed,
# respecting existing schedules and the constraint that Arthur cannot meet on Tuesday.

from typing import List, Tuple, Dict

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_time_str(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

def subtract_busy(work: Tuple[int, int], busy: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    # Returns free intervals within 'work' after subtracting 'busy' intervals.
    ws, we = work
    busy_sorted = sorted(busy)
    free = []
    cur = ws
    for bs, be in busy_sorted:
        if be <= ws or bs >= we:
            continue
        s = max(bs, ws)
        e = min(be, we)
        if s > cur:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < we:
        free.append((cur, we))
    return free

def intersect_intervals(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    # Intersects two lists of intervals.
    i = j = 0
    inter = []
    while i < len(a) and j < len(b):
        s = max(a[i][0], b[j][0])
        e = min(a[i][1], b[j][1])
        if s < e:
            inter.append((s, e))
        if a[i][1] < b[j][1]:
            i += 1
        else:
            j += 1
    return inter

def earliest_slot(intervals: List[Tuple[int, int]], duration: int) -> Tuple[int, int] or None:
    for s, e in intervals:
        if e - s >= duration:
            return (s, s + duration)
    return None

# Input data
work_hours = (to_minutes("09:00"), to_minutes("17:00"))
duration = 30  # minutes

days = ["Monday", "Tuesday", "Wednesday"]

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

# Constraints: Arthur cannot meet on Tuesday
allowed_days = [d for d in days if d != "Tuesday"]

# Find earliest possible meeting
for day in allowed_days:
    arthur_free = subtract_busy(work_hours, arthur_busy.get(day, []))
    michael_free = subtract_busy(work_hours, michael_busy.get(day, []))
    overlap = intersect_intervals(arthur_free, michael_free)
    slot = earliest_slot(overlap, duration)
    if slot:
        start_str = to_time_str(slot[0])
        end_str = to_time_str(slot[1])
        print(f"{day} {{{start_str}:{end_str}}}")
        break