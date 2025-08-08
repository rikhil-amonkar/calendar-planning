from typing import List, Tuple

def parse_time(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def fmt_time(minutes: int) -> str:
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

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

def invert_intervals(busy: List[Tuple[int, int]], start: int, end: int) -> List[Tuple[int, int]]:
    if not busy:
        return [(start, end)]
    free = []
    cur = start
    for s, e in busy:
        if s > cur:
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

def earliest_slot(common_free: List[Tuple[int, int]], duration: int) -> Tuple[int, int]:
    for s, e in common_free:
        if e - s >= duration:
            return (s, s + duration)
    raise ValueError("No suitable slot found")

def main():
    day = "Monday"
    work_start_str, work_end_str = "09:00", "17:00"
    duration_minutes = 30  # half an hour

    participants_busy_str = {
        "Adam": [("09:30", "10:00"), ("12:30", "13:00"), ("14:30", "15:00"), ("16:30", "17:00")],
        "Roy":  [("10:00", "11:00"), ("11:30", "13:00"), ("13:30", "14:30"), ("16:30", "17:00")],
    }

    work_start = parse_time(work_start_str)
    work_end = parse_time(work_end_str)

    # Prepare free intervals for each participant within work hours
    all_free = []
    for slots in participants_busy_str.values():
        busy = [(max(parse_time(s), work_start), min(parse_time(e), work_end)) for s, e in slots]
        busy = [(s, e) for s, e in busy if s < e]  # clip to work hours
        busy_merged = merge_intervals(busy)
        free = invert_intervals(busy_merged, work_start, work_end)
        all_free.append(free)

    # Intersect free intervals across all participants
    common_free = all_free[0]
    for free in all_free[1:]:
        common_free = intersect_two(common_free, free)

    # Find earliest suitable slot
    start_min, end_min = earliest_slot(common_free, duration_minutes)
    start_str, end_str = fmt_time(start_min), fmt_time(end_min)

    # Output: time range in {HH:MM:HH:MM} and the day of the week
    print(f"{{{start_str}:{end_str}}}")
    print(day)

if __name__ == "__main__":
    main()