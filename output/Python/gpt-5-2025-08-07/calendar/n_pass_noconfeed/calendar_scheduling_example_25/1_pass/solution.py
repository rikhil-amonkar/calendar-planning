# Meeting scheduler for Anthony, Pamela, and Zachary on Monday

from typing import List, Tuple

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
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

def clamp_intervals(intervals: List[Tuple[int, int]], start: int, end: int) -> List[Tuple[int, int]]:
    clamped = []
    for s, e in intervals:
        s = max(s, start)
        e = min(e, end)
        if s < e:
            clamped.append((s, e))
    return clamped

def invert_busy_to_free(busy: List[Tuple[int, int]], start: int, end: int) -> List[Tuple[int, int]]:
    busy = merge_intervals(clamp_intervals(busy, start, end))
    free = []
    cur = start
    for s, e in busy:
        if cur < s:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < end:
        free.append((cur, end))
    return free

def intersect_two(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
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

def intersect_all(lists: List[List[Tuple[int, int]]]) -> List[Tuple[int, int]]:
    if not lists:
        return []
    res = lists[0]
    for lst in lists[1:]:
        res = intersect_two(res, lst)
        if not res:
            break
    return res

def find_slot(free_intersections: List[Tuple[int, int]], duration: int) -> Tuple[int, int]:
    for s, e in free_intersections:
        if e - s >= duration:
            return (s, s + duration)
    return (-1, -1)

def main():
    day = "Monday"
    work_start = to_minutes("09:00")
    work_end = to_minutes("17:00")
    duration = 60  # minutes

    # Busy schedules
    anthony_busy = [("09:30","10:00"), ("12:00","13:00"), ("16:00","16:30")]
    pamela_busy  = [("09:30","10:00"), ("16:30","17:00")]
    zach_busy    = [("09:00","11:30"), ("12:00","12:30"), ("13:00","13:30"), ("14:30","15:00"), ("16:00","17:00")]

    # Convert to minutes
    anthony_busy_m = [(to_minutes(s), to_minutes(e)) for s, e in anthony_busy]
    pamela_busy_m  = [(to_minutes(s), to_minutes(e)) for s, e in pamela_busy]
    zach_busy_m    = [(to_minutes(s), to_minutes(e)) for s, e in zach_busy]

    # Pamela's preference: do not meet after 14:30 (meeting must end by 14:30)
    pamela_end_cap = to_minutes("14:30")

    # Compute free intervals within work hours
    anthony_free = invert_busy_to_free(anthony_busy_m, work_start, work_end)
    # For Pamela, cap her day to end by 14:30
    pamela_free  = invert_busy_to_free(pamela_busy_m, work_start, min(work_end, pamela_end_cap))
    zach_free    = invert_busy_to_free(zach_busy_m, work_start, work_end)

    # Intersect all free intervals
    common_free = intersect_all([anthony_free, pamela_free, zach_free])

    # Find the earliest slot of required duration
    start, end = find_slot(common_free, duration)

    # Output
    if start >= 0:
        time_range = f"{to_hhmm(start)}:{to_hhmm(end)}"
        print(day)
        print(f"{{{time_range}}}")
    else:
        # Problem statement guarantees a solution exists, but handle just in case
        print(day)
        print("{No available slot}")

if __name__ == "__main__":
    main()