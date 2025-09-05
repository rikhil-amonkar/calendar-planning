from typing import List, Tuple, Dict

# Helper functions
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

def invert_within(work: Tuple[int, int], busy: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    ws, we = work
    busy = merge_intervals([(max(ws, s), min(we, e)) for s, e in busy if e > ws and s < we])
    free = []
    cur = ws
    for s, e in busy:
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

# Problem data
work_window = (to_minutes("09:00"), to_minutes("17:00"))
duration = 60  # minutes
days = ["Monday", "Tuesday"]

schedules: Dict[str, Dict[str, List[Tuple[int, int]]]] = {
    "Monday": {
        "Gary": [
            (to_minutes("09:30"), to_minutes("10:00")),
            (to_minutes("11:00"), to_minutes("13:00")),
            (to_minutes("14:00"), to_minutes("14:30")),
            (to_minutes("16:30"), to_minutes("17:00")),
        ],
        "David": [
            (to_minutes("09:00"), to_minutes("09:30")),
            (to_minutes("10:00"), to_minutes("13:00")),
            (to_minutes("14:30"), to_minutes("16:30")),
        ],
    },
    "Tuesday": {
        "Gary": [
            (to_minutes("09:00"), to_minutes("09:30")),
            (to_minutes("10:30"), to_minutes("11:00")),
            (to_minutes("14:30"), to_minutes("16:00")),
        ],
        "David": [
            (to_minutes("09:00"), to_minutes("09:30")),
            (to_minutes("10:00"), to_minutes("10:30")),
            (to_minutes("11:00"), to_minutes("12:30")),
            (to_minutes("13:00"), to_minutes("14:30")),
            (to_minutes("15:00"), to_minutes("16:00")),
            (to_minutes("16:30"), to_minutes("17:00")),
        ],
    },
}

# Find earliest feasible slot
for day in days:
    g_free = invert_within(work_window, schedules[day]["Gary"])
    d_free = invert_within(work_window, schedules[day]["David"])
    joint = intersect_intervals(g_free, d_free)
    for s, e in joint:
        if e - s >= duration:
            start = s
            end = s + duration
            print(f"{day} {{{to_hhmm(start)}:{to_hhmm(end)}}}")
            raise SystemExit

# Fallback (should not happen per problem statement)
print("No suitable slot found")