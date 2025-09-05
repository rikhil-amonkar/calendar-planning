from typing import List, Tuple

# Helper functions
def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def fmt_time(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

def subtract_from_window(busy: List[Tuple[int, int]], window: Tuple[int, int]) -> List[Tuple[int, int]]:
    ws, we = window
    # Normalize and sort busy intervals, clipped to window
    normalized = []
    for s, e in sorted(busy):
        s = max(ws, s)
        e = min(we, e)
        if s < e:
            normalized.append((s, e))
    # Build free intervals
    free = []
    cur = ws
    for s, e in normalized:
        if cur < s:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < we:
        free.append((cur, we))
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

# Inputs
day = "Monday"
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
window = (work_start, work_end)
duration = 30  # minutes

schedules = {
    "Judy":        [(to_minutes("13:00"), to_minutes("13:30")), (to_minutes("16:00"), to_minutes("16:30"))],
    "Olivia":      [(to_minutes("10:00"), to_minutes("10:30")), (to_minutes("12:00"), to_minutes("13:00")), (to_minutes("14:00"), to_minutes("14:30"))],
    "Eric":        [],  # free all day
    "Jacqueline":  [(to_minutes("10:00"), to_minutes("10:30")), (to_minutes("15:00"), to_minutes("15:30"))],
    "Laura":       [(to_minutes("09:00"), to_minutes("10:00")), (to_minutes("10:30"), to_minutes("12:00")), (to_minutes("13:00"), to_minutes("13:30")), (to_minutes("14:30"), to_minutes("15:00")), (to_minutes("15:30"), to_minutes("17:00"))],
    "Tyler":       [(to_minutes("09:00"), to_minutes("10:00")), (to_minutes("11:00"), to_minutes("11:30")), (to_minutes("12:30"), to_minutes("13:00")), (to_minutes("14:00"), to_minutes("14:30")), (to_minutes("15:30"), to_minutes("17:00"))],
    "Lisa":        [(to_minutes("09:30"), to_minutes("10:30")), (to_minutes("11:00"), to_minutes("11:30")), (to_minutes("12:00"), to_minutes("12:30")), (to_minutes("13:00"), to_minutes("13:30")), (to_minutes("14:00"), to_minutes("14:30")), (to_minutes("16:00"), to_minutes("17:00"))],
}

# Compute each participant's free intervals within work window
free_by_person = {p: subtract_from_window(busy, window) for p, busy in schedules.items()}

# Intersect all free intervals to find common availability
common_free = [(work_start, work_end)]
for p in free_by_person:
    common_free = intersect_intervals(common_free, free_by_person[p])

# Find the earliest slot that fits the duration
meeting_start = meeting_end = None
for s, e in common_free:
    if e - s >= duration:
        meeting_start = s
        meeting_end = s + duration
        break

# Output
if meeting_start is not None:
    time_range = f"{fmt_time(meeting_start)}:{fmt_time(meeting_end)}"
    print(f"{day} {{{time_range}}}")
else:
    # As per prompt, a solution exists; this fallback would rarely trigger.
    print(f"{day} {{No available slot}}")