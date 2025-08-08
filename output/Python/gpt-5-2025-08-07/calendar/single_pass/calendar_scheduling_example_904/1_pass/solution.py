from typing import List, Tuple, Dict

# Time helpers
def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

Interval = Tuple[int, int]

def merge_intervals(intervals: List[Interval]) -> List[Interval]:
    if not intervals:
        return []
    intervals.sort()
    merged = [intervals[0]]
    for s, e in intervals[1:]:
        ls, le = merged[-1]
        if s <= le:
            merged[-1] = (ls, max(le, e))
        else:
            merged.append((s, e))
    return merged

def invert_intervals(busy: List[Interval], start: int, end: int) -> List[Interval]:
    free = []
    cur = start
    for s, e in busy:
        if s > cur:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < end:
        free.append((cur, end))
    return free

def intersect_intervals(a: List[Interval], b: List[Interval]) -> List[Interval]:
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

# Work hours and meeting duration
WORK_START = to_minutes("09:00")
WORK_END   = to_minutes("17:00")
DURATION   = 30

days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]

# Schedules
daniel_busy: Dict[str, List[Interval]] = {
    "Monday":    [(to_minutes("09:30"), to_minutes("10:30")),
                  (to_minutes("12:00"), to_minutes("12:30")),
                  (to_minutes("13:00"), to_minutes("14:00")),
                  (to_minutes("14:30"), to_minutes("15:00")),
                  (to_minutes("15:30"), to_minutes("16:00"))],
    "Tuesday":   [(to_minutes("11:00"), to_minutes("12:00")),
                  (to_minutes("13:00"), to_minutes("13:30")),
                  (to_minutes("15:30"), to_minutes("16:00")),
                  (to_minutes("16:30"), to_minutes("17:00"))],
    "Wednesday": [(to_minutes("09:00"), to_minutes("10:00")),
                  (to_minutes("14:00"), to_minutes("14:30"))],
    "Thursday":  [(to_minutes("10:30"), to_minutes("11:00")),
                  (to_minutes("12:00"), to_minutes("13:00")),
                  (to_minutes("14:30"), to_minutes("15:00")),
                  (to_minutes("15:30"), to_minutes("16:00"))],
    "Friday":    [(to_minutes("09:00"), to_minutes("09:30")),
                  (to_minutes("11:30"), to_minutes("12:00")),
                  (to_minutes("13:00"), to_minutes("13:30")),
                  (to_minutes("16:30"), to_minutes("17:00"))],
}

bradley_busy: Dict[str, List[Interval]] = {
    "Monday":    [(to_minutes("09:30"), to_minutes("11:00")),
                  (to_minutes("11:30"), to_minutes("12:00")),
                  (to_minutes("12:30"), to_minutes("13:00")),
                  (to_minutes("14:00"), to_minutes("15:00"))],
    "Tuesday":   [(to_minutes("10:30"), to_minutes("11:00")),
                  (to_minutes("12:00"), to_minutes("13:00")),
                  (to_minutes("13:30"), to_minutes("14:00")),
                  (to_minutes("15:30"), to_minutes("16:30"))],
    "Wednesday": [(to_minutes("09:00"), to_minutes("10:00")),
                  (to_minutes("11:00"), to_minutes("13:00")),
                  (to_minutes("13:30"), to_minutes("14:00")),
                  (to_minutes("14:30"), to_minutes("17:00"))],
    "Thursday":  [(to_minutes("09:00"), to_minutes("12:30")),
                  (to_minutes("13:30"), to_minutes("14:00")),
                  (to_minutes("14:30"), to_minutes("15:00")),
                  (to_minutes("15:30"), to_minutes("16:30"))],
    "Friday":    [(to_minutes("09:00"), to_minutes("09:30")),
                  (to_minutes("10:00"), to_minutes("12:30")),
                  (to_minutes("13:00"), to_minutes("13:30")),
                  (to_minutes("14:00"), to_minutes("14:30")),
                  (to_minutes("15:30"), to_minutes("16:30"))],
}

# Merge busy intervals and compute free intervals per person/day
def day_free(busy: Dict[str, List[Interval]], day: str) -> List[Interval]:
    merged = merge_intervals(busy.get(day, []))
    return invert_intervals(merged, WORK_START, WORK_END)

daniel_avoid_soft = {"Wednesday", "Thursday"}  # "would rather not"
# Bradley hard constraints:
hard_exclude_days = {"Monday", "Friday"}       # do not want to meet these days
min_start_by_day: Dict[str, int] = {d: WORK_START for d in days}
# Bradley: Tuesday before 12:00 not allowed
min_start_by_day["Tuesday"] = max(min_start_by_day["Tuesday"], to_minutes("12:00"))

def find_slot(candidate_days: List[str]) -> Tuple[str, int, int]:
    for day in candidate_days:
        if day in hard_exclude_days:
            continue
        dfree = day_free(daniel_busy, day)
        bfree = day_free(bradley_busy, day)
        common = intersect_intervals(dfree, bfree)
        if not common:
            continue
        min_start = min_start_by_day.get(day, WORK_START)
        for s, e in common:
            start = max(s, min_start)
            if start + DURATION <= e:
                return day, start, start + DURATION
    return "", -1, -1

# First, try to honor Daniel's soft preferences (avoid Wed/Thu)
preferred_days = [d for d in days if d not in daniel_avoid_soft]
day, start, end = find_slot(preferred_days)

# If none found, allow all non-hard-excluded days (shouldn't be needed here)
if day == "":
    fallback_days = [d for d in days if d not in hard_exclude_days]
    day, start, end = find_slot(fallback_days)

# Output
if day != "":
    print(f"{day} {{{to_hhmm(start)}:{to_hhmm(end)}}}")
else:
    print("No feasible time found")