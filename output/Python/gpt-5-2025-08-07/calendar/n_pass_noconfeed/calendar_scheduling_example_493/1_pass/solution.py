from typing import List, Tuple

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

def complement_within(busy: List[Tuple[int, int]], start: int, end: int) -> List[Tuple[int, int]]:
    if start >= end:
        return []
    busy = [(max(start, s), min(end, e)) for s, e in busy if min(end, e) > max(start, s)]
    busy = merge_intervals(busy)
    free = []
    prev = start
    for s, e in busy:
        if s > prev:
            free.append((prev, s))
        prev = max(prev, e)
    if prev < end:
        free.append((prev, end))
    return free

def intersect(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    i = j = 0
    result = []
    while i < len(a) and j < len(b):
        s = max(a[i][0], b[j][0])
        e = min(a[i][1], b[j][1])
        if s < e:
            result.append((s, e))
        if a[i][1] < b[j][1]:
            i += 1
        else:
            j += 1
    return result

def find_slot(all_free: List[List[Tuple[int, int]]], duration: int) -> Tuple[int, int]:
    # Intersect all participants' free intervals
    common = all_free[0]
    for free in all_free[1:]:
        common = intersect(common, free)
        if not common:
            break
    for s, e in common:
        if e - s >= duration:
            return s, s + duration
    raise ValueError("No suitable slot found")

def main():
    day = "Monday"
    work_start, work_end = to_minutes("09:00"), to_minutes("17:00")
    duration = 30  # minutes

    schedules_busy = {
        "Tyler": [],
        "Kelly": [],
        "Stephanie": [("11:00", "11:30"), ("14:30", "15:00")],
        "Hannah": [],
        "Joe": [("09:00", "09:30"), ("10:00", "12:00"), ("12:30", "13:00"), ("14:00", "17:00")],
        "Diana": [("09:00", "10:30"), ("11:30", "12:00"), ("13:00", "14:00"), ("14:30", "15:30"), ("16:00", "17:00")],
        "Deborah": [("09:00", "10:00"), ("10:30", "12:00"), ("12:30", "13:00"), ("13:30", "14:00"), ("14:30", "15:30"), ("16:00", "16:30")],
    }

    # Convert busy schedules to minutes and compute free intervals within work hours
    all_free = []
    for person, intervals in schedules_busy.items():
        busy_minutes = [(to_minutes(s), to_minutes(e)) for s, e in intervals]
        free = complement_within(busy_minutes, work_start, work_end)
        all_free.append(free)

    start, end = find_slot(all_free, duration)
    time_range = f"{to_hhmm(start)}:{to_hhmm(end)}"

    # Output: time range in braces and the day of the week
    print(f"{{{time_range}}}")
    print(day)

if __name__ == "__main__":
    main()