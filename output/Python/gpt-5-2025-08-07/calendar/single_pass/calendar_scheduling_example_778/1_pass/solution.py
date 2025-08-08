# Meeting scheduler for Susan and Sandra
# Finds a 30-minute slot between 09:00 and 17:00 on Mon/Tue/Wed
# honoring: Susan would rather not meet on Tuesday (soft preference)
# and Sandra cannot meet on Monday after 16:00 (hard constraint).

from typing import List, Tuple, Dict

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m//60:02d}:{m%60:02d}"

def merge_intervals(intervals: List[Tuple[int,int]]) -> List[Tuple[int,int]]:
    if not intervals:
        return []
    intervals = sorted(intervals)
    merged = [intervals[0]]
    for s, e in intervals[1:]:
        ls, le = merged[-1]
        if s <= le:
            merged[-1] = (ls, max(le, e))
        else:
            merged.append((s, e))
    return merged

def invert_to_free(busy: List[Tuple[int,int]], day_start: int, day_end: int) -> List[Tuple[int,int]]:
    busy = merge_intervals([b for b in busy if b[0] < b[1]])
    free = []
    cur = day_start
    for s, e in busy:
        if cur < s:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < day_end:
        free.append((cur, day_end))
    return free

def intersect_intervals(a: List[Tuple[int,int]], b: List[Tuple[int,int]]) -> List[Tuple[int,int]]:
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

# Work hours and meeting duration
DAY_START = to_minutes("09:00")
DAY_END   = to_minutes("17:00")
DURATION  = 30  # minutes

# Busy schedules
susan_busy: Dict[str, List[Tuple[int,int]]] = {
    "Monday":    [(to_minutes("12:30"), to_minutes("13:00")),
                  (to_minutes("13:30"), to_minutes("14:00"))],
    "Tuesday":   [(to_minutes("11:30"), to_minutes("12:00"))],
    "Wednesday": [(to_minutes("09:30"), to_minutes("10:30")),
                  (to_minutes("14:00"), to_minutes("14:30")),
                  (to_minutes("15:30"), to_minutes("16:30"))],
}

sandra_busy: Dict[str, List[Tuple[int,int]]] = {
    "Monday":    [(to_minutes("09:00"), to_minutes("13:00")),
                  (to_minutes("14:00"), to_minutes("15:00")),
                  (to_minutes("16:00"), to_minutes("16:30"))],
    "Tuesday":   [(to_minutes("09:00"), to_minutes("09:30")),
                  (to_minutes("10:30"), to_minutes("12:00")),
                  (to_minutes("12:30"), to_minutes("13:30")),
                  (to_minutes("14:00"), to_minutes("14:30")),
                  (to_minutes("16:00"), to_minutes("17:00"))],
    "Wednesday": [(to_minutes("09:00"), to_minutes("11:30")),
                  (to_minutes("12:00"), to_minutes("12:30")),
                  (to_minutes("13:00"), to_minutes("17:00"))],
}

# Apply hard constraint: Sandra cannot meet Monday after 16:00
sandra_busy["Monday"] = sandra_busy["Monday"] + [(to_minutes("16:00"), to_minutes("17:00"))]

# Preference: avoid Tuesday if possible (soft). So check in this priority order.
day_priority = ["Monday", "Wednesday", "Tuesday"]

def find_slot() -> Tuple[str, int, int]:
    for day in day_priority:
        susan_free = invert_to_free(susan_busy.get(day, []), DAY_START, DAY_END)
        sandra_free = invert_to_free(sandra_busy.get(day, []), DAY_START, DAY_END)
        common = intersect_intervals(susan_free, sandra_free)
        # find earliest slot of at least DURATION
        for s, e in common:
            if e - s >= DURATION:
                return day, s, s + DURATION
    raise RuntimeError("No feasible slot found (but problem states one exists).")

day, start_min, end_min = find_slot()
start_str = to_hhmm(start_min)
end_str = to_hhmm(end_min)

# Output must include both the time range (HH:MM:HH:MM) and the day of the week.
print(day)
print(f"{start_str}:{end_str}")