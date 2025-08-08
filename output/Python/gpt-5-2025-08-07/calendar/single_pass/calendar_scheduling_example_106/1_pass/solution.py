from typing import List, Tuple

def parse_time(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def format_time(minutes: int) -> str:
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def normalize_intervals(intervals: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    # Merge overlapping intervals and sort
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

def complement_within(intervals: List[Tuple[int, int]], window: Tuple[int, int]) -> List[Tuple[int, int]]:
    ws, we = window
    if not intervals:
        return [(ws, we)]
    intervals = [(max(ws, s), min(we, e)) for s, e in intervals if e > ws and s < we]
    intervals = normalize_intervals(intervals)
    free = []
    cur = ws
    for s, e in intervals:
        if s > cur:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < we:
        free.append((cur, we))
    return free

def intersect(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
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

def find_slot(common_free: List[Tuple[int, int]], duration: int) -> Tuple[int, int]:
    for s, e in common_free:
        if e - s >= duration:
            return s, s + duration
    raise ValueError("No suitable slot found")

def main():
    day = "Monday"
    work_start, work_end = parse_time("09:00"), parse_time("17:00")
    duration = 60  # minutes

    schedules = {
        "Olivia": [("12:30","13:30"), ("14:30","15:00"), ("16:30","17:00")],
        "Anna": [],
        "Virginia": [("09:00","10:00"), ("11:30","16:00"), ("16:30","17:00")],
        "Paul": [("09:00","09:30"), ("11:00","11:30"), ("13:00","14:00"), ("14:30","16:00"), ("16:30","17:00")],
    }

    window = (work_start, work_end)

    # Compute free intervals for each participant
    all_free = []
    for blocks in schedules.values():
        blocked = [(parse_time(s), parse_time(e)) for s, e in blocks]
        free = complement_within(blocked, window)
        all_free.append(free)

    # Intersect all free intervals
    common = [(work_start, work_end)]
    for free in all_free:
        common = intersect(common, free)
        if not common:
            break

    start, end = find_slot(common, duration)
    start_str, end_str = format_time(start), format_time(end)

    # Output: day and time range in {HH:MM:HH:MM} format
    print(day)
    print(f"{{{start_str}:{end_str}}}")

if __name__ == "__main__":
    main()