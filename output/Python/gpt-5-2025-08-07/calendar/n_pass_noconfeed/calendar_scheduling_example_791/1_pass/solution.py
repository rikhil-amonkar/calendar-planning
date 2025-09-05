from typing import List, Tuple, Dict

# Utilities
def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m//60:02d}:{m%60:02d}"

def merge_intervals(intervals: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
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

def invert_intervals(busy: List[Tuple[int, int]], bounds: Tuple[int, int]) -> List[Tuple[int, int]]:
    start, end = bounds
    if not busy:
        return [(start, end)]
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

def intersect(a: List[Tuple[int,int]], b: List[Tuple[int,int]]) -> List[Tuple[int,int]]:
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

def clamp_intervals(intervals: List[Tuple[int,int]], limit: Tuple[int,int]) -> List[Tuple[int,int]]:
    ls, le = limit
    out = []
    for s, e in intervals:
        ns, ne = max(s, ls), min(e, le)
        if ns < ne:
            out.append((ns, ne))
    return out

# Problem setup
days = ["Monday", "Tuesday", "Wednesday"]
WORK_START, WORK_END = to_minutes("09:00"), to_minutes("17:00")
WORK_BOUNDS = (WORK_START, WORK_END)
MEETING_DURATION = 30  # minutes

# Busy schedules
nicole_busy: Dict[str, List[Tuple[int,int]]] = {
    "Monday":    [(to_minutes("09:00"), to_minutes("09:30")),
                  (to_minutes("13:00"), to_minutes("13:30")),
                  (to_minutes("14:30"), to_minutes("15:30"))],
    "Tuesday":   [(to_minutes("09:00"), to_minutes("09:30")),
                  (to_minutes("11:30"), to_minutes("13:30")),
                  (to_minutes("14:30"), to_minutes("15:30"))],
    "Wednesday": [(to_minutes("10:00"), to_minutes("11:00")),
                  (to_minutes("12:30"), to_minutes("15:00")),
                  (to_minutes("16:00"), to_minutes("17:00"))],
}

ruth_busy: Dict[str, List[Tuple[int,int]]] = {
    "Monday":    [(to_minutes("09:00"), to_minutes("17:00"))],
    "Tuesday":   [(to_minutes("09:00"), to_minutes("17:00"))],
    "Wednesday": [(to_minutes("09:00"), to_minutes("10:30")),
                  (to_minutes("11:00"), to_minutes("11:30")),
                  (to_minutes("12:00"), to_minutes("12:30")),
                  (to_minutes("13:30"), to_minutes("15:30")),
                  (to_minutes("16:00"), to_minutes("16:30"))],
}

# Preference: Ruth does not want to meet on Wednesday after 13:30
WED_LATEST_END = to_minutes("13:30")

def find_meeting() -> Tuple[str, int, int]:
    for day in days:
        nic_free = invert_intervals(nicole_busy.get(day, []), WORK_BOUNDS)
        ruth_free = invert_intervals(ruth_busy.get(day, []), WORK_BOUNDS)

        # Apply Wednesday preference (meeting must end by 13:30)
        if day == "Wednesday":
            ruth_free = clamp_intervals(ruth_free, (WORK_START, WED_LATEST_END))

        common = intersect(nic_free, ruth_free)
        for s, e in common:
            if e - s >= MEETING_DURATION:
                return day, s, s + MEETING_DURATION
    raise RuntimeError("No feasible slot found")

if __name__ == "__main__":
    day, start, end = find_meeting()
    time_range = f"{{{to_hhmm(start)}:{to_hhmm(end)}}}"
    print(day, time_range)