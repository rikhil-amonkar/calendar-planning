from typing import List, Tuple, Dict

# Meeting parameters
WORK_START = "09:00"
WORK_END = "17:00"
MEETING_MINUTES = 60

# Prefer to avoid Monday; search Tue-Fri first, then Monday if needed
DAYS_ORDER_PRIMARY = ["Tuesday", "Wednesday", "Thursday", "Friday"]
DAYS_ORDER_FALLBACK = ["Monday"]

# Participants' busy schedules
brian_busy: Dict[str, List[Tuple[str, str]]] = {
    "Monday":    [("09:30", "10:00"), ("12:30", "14:30"), ("15:30", "16:00")],
    "Tuesday":   [("09:00", "09:30")],
    "Wednesday": [("12:30", "14:00"), ("16:30", "17:00")],
    "Thursday":  [("11:00", "11:30"), ("13:00", "13:30"), ("16:30", "17:00")],
    "Friday":    [("09:30", "10:00"), ("10:30", "11:00"), ("13:00", "13:30"), ("15:00", "16:00"), ("16:30", "17:00")],
}
julia_busy: Dict[str, List[Tuple[str, str]]] = {
    "Monday":    [("09:00", "10:00"), ("11:00", "11:30"), ("12:30", "13:00"), ("15:30", "16:00")],
    "Tuesday":   [("13:00", "14:00"), ("16:00", "16:30")],
    "Wednesday": [("09:00", "11:30"), ("12:00", "12:30"), ("13:00", "17:00")],
    "Thursday":  [("09:00", "10:30"), ("11:00", "17:00")],
    "Friday":    [("09:00", "10:00"), ("10:30", "11:30"), ("12:30", "14:00"), ("14:30", "15:00"), ("15:30", "16:00")],
}

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

def normalize_and_clip(busy: List[Tuple[int, int]], ws: int, we: int) -> List[Tuple[int, int]]:
    # Clip to work hours and remove invalid/empty intervals
    clipped = []
    for s, e in busy:
        s = max(s, ws)
        e = min(e, we)
        if e > s:
            clipped.append((s, e))
    # Merge overlaps
    clipped.sort()
    merged = []
    for s, e in clipped:
        if not merged or s > merged[-1][1]:
            merged.append((s, e))
        else:
            merged[-1] = (merged[-1][0], max(merged[-1][1], e))
    return merged

def invert_to_free(busy: List[Tuple[int, int]], ws: int, we: int) -> List[Tuple[int, int]]:
    free = []
    cur = ws
    for s, e in busy:
        if s > cur:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < we:
        free.append((cur, we))
    return free

def intersect_intervals(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    i = j = 0
    out = []
    while i < len(a) and j < len(b):
        s = max(a[i][0], b[j][0])
        e = min(a[i][1], b[j][1])
        if e > s:
            out.append((s, e))
        if a[i][1] < b[j][1]:
            i += 1
        else:
            j += 1
    return out

def earliest_slot_on_day(day: str) -> Tuple[str, str]:
    ws, we = to_minutes(WORK_START), to_minutes(WORK_END)

    brian_b = normalize_and_clip([(to_minutes(s), to_minutes(e)) for s, e in brian_busy.get(day, [])], ws, we)
    julia_b = normalize_and_clip([(to_minutes(s), to_minutes(e)) for s, e in julia_busy.get(day, [])], ws, we)

    brian_free = invert_to_free(brian_b, ws, we)
    julia_free = invert_to_free(julia_b, ws, we)

    common_free = intersect_intervals(brian_free, julia_free)

    for s, e in common_free:
        if e - s >= MEETING_MINUTES:
            start = s
            end = s + MEETING_MINUTES
            return to_hhmm(start), to_hhmm(end)
    return "", ""

def find_meeting() -> Tuple[str, str, str]:
    # Try preferred days (avoid Monday)
    for day in DAYS_ORDER_PRIMARY:
        start, end = earliest_slot_on_day(day)
        if start:
            return day, start, end
    # Fallback to Monday if necessary
    for day in DAYS_ORDER_FALLBACK:
        start, end = earliest_slot_on_day(day)
        if start:
            return day, start, end
    # Given the problem statement, this should not happen
    return "", "", ""

if __name__ == "__main__":
    day, start, end = find_meeting()
    if day:
        print(f"{day} {{{start}:{end}}}")
    else:
        print("No available slot found.")