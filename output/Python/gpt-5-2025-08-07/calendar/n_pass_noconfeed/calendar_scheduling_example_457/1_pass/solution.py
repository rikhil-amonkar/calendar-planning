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

def complement_within(bounds: Tuple[int, int], busy: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    start, end = bounds
    free = []
    cursor = start
    for s, e in busy:
        s = max(start, s)
        e = min(end, e)
        if e <= start or s >= end:
            continue
        if cursor < s:
            free.append((cursor, s))
        cursor = max(cursor, e)
    if cursor < end:
        free.append((cursor, end))
    return free

def find_slot(free_intervals: List[Tuple[int, int]], duration: int) -> Tuple[int, int]:
    for s, e in free_intervals:
        if e - s >= duration:
            return (s, s + duration)
    raise ValueError("No slot found")

def main():
    day = "Monday"
    work_start, work_end = to_minutes("09:00"), to_minutes("17:00")
    duration = 30  # minutes

    schedules = {
        "Andrea": [("09:30","10:30"), ("13:30","14:30")],
        "Ruth":   [("12:30","13:00"), ("15:00","15:30")],
        "Steven": [("10:00","10:30"), ("11:00","11:30"), ("12:00","12:30"), ("13:30","14:00"), ("15:00","16:00")],
        "Grace":  [],
        "Kyle":   [("09:00","09:30"), ("10:30","12:00"), ("12:30","13:00"), ("13:30","15:00"), ("15:30","16:00"), ("16:30","17:00")],
        "Elijah": [("09:00","11:00"), ("11:30","13:00"), ("13:30","14:00"), ("15:30","16:00"), ("16:30","17:00")],
        "Lori":   [("09:00","09:30"), ("10:00","11:30"), ("12:00","13:30"), ("14:00","16:00"), ("16:30","17:00")]
    }

    # Flatten and clip all busy intervals to work hours
    all_busy: List[Tuple[int, int]] = []
    for person, intervals in schedules.items():
        for s, e in intervals:
            sm, em = to_minutes(s), to_minutes(e)
            # clip to work bounds if overlapping
            if em <= work_start or sm >= work_end:
                continue
            all_busy.append((max(work_start, sm), min(work_end, em)))

    # Merge all busy intervals to get times when anyone is busy
    merged_busy = merge_intervals(all_busy)

    # Complement within work hours gives times when everyone is free
    everyone_free = complement_within((work_start, work_end), merged_busy)

    # Find earliest slot of required duration
    start, end = find_slot(everyone_free, duration)

    # Output in required format
    print(f"{to_hhmm(start)}:{to_hhmm(end)}")
    print(day)

if __name__ == "__main__":
    main()