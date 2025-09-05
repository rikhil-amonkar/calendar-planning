from typing import List, Tuple

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

def subtract_busy(window: Tuple[int, int], busy: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    start, end = window
    # Normalize and clip busy intervals to the window
    clipped = []
    for b_start, b_end in busy:
        if b_end <= start or b_start >= end:
            continue
        clipped.append((max(start, b_start), min(end, b_end)))
    clipped.sort()
    # Merge overlaps
    merged = []
    for s, e in clipped:
        if not merged or s > merged[-1][1]:
            merged.append([s, e])
        else:
            merged[-1][1] = max(merged[-1][1], e)
    # Build free intervals
    free = []
    cur = start
    for s, e in merged:
        if cur < s:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < end:
        free.append((cur, end))
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

def first_slot(intervals: List[Tuple[int, int]], duration: int) -> Tuple[int, int]:
    for s, e in intervals:
        if e - s >= duration:
            return s, s + duration
    raise ValueError("No suitable slot found")

def main():
    day = "Monday"
    meeting_duration = 30  # minutes
    work_start, work_end = to_minutes("09:00"), to_minutes("17:00")

    # Deborah: free all day within work hours
    deborah_busy = []

    # Albert: busy slots plus cannot meet after 11:00 -> treat as busy from 11:00 to end of work day
    albert_busy = [
        (to_minutes("09:00"), to_minutes("10:00")),
        (to_minutes("10:30"), to_minutes("12:00")),
        (to_minutes("15:00"), to_minutes("16:30")),
        (to_minutes("11:00"), work_end),  # cannot meet after 11:00
    ]

    deborah_free = subtract_busy((work_start, work_end), deborah_busy)
    albert_free = subtract_busy((work_start, work_end), albert_busy)

    common_free = intersect_intervals(deborah_free, albert_free)
    start, end = first_slot(common_free, meeting_duration)

    time_range = f"{{{to_hhmm(start)}:{to_hhmm(end)}}}"
    print(time_range)
    print(day)

if __name__ == "__main__":
    main()