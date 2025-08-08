from typing import List, Tuple

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

def clip(interval: Tuple[int, int], bounds: Tuple[int, int]) -> Tuple[int, int] | None:
    s, e = interval
    bs, be = bounds
    s, e = max(s, bs), min(e, be)
    return (s, e) if s < e else None

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

def complement_within(bounds: Tuple[int, int], blocked: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    bs, be = bounds
    free = []
    prev_end = bs
    for s, e in blocked:
        if prev_end < s:
            free.append((prev_end, s))
        prev_end = max(prev_end, e)
    if prev_end < be:
        free.append((prev_end, be))
    return free

def find_slot(free_intervals: List[Tuple[int, int]], duration: int) -> Tuple[int, int] | None:
    for s, e in free_intervals:
        if e - s >= duration:
            return (s, s + duration)
    return None

def main():
    day = "Monday"
    work_start = to_minutes("09:00")
    work_end = to_minutes("17:00")
    work_bounds = (work_start, work_end)
    duration_minutes = 30

    schedules = {
        "Walter": [],
        "Cynthia": [("09:00","09:30"), ("10:00","10:30"), ("13:30","14:30"), ("15:00","16:00")],
        "Ann": [("10:00","11:00"), ("13:00","13:30"), ("14:00","15:00"), ("16:00","16:30")],
        "Catherine": [("09:00","11:30"), ("12:30","13:30"), ("14:30","17:00")],
        "Kyle": [("09:00","09:30"), ("10:00","11:30"), ("12:00","12:30"), ("13:00","14:30"), ("15:00","16:00")],
    }

    # Collect all busy intervals across all participants, clipped to working hours
    all_busy: List[Tuple[int, int]] = []
    for meetings in schedules.values():
        for s, e in meetings:
            clipped = clip((to_minutes(s), to_minutes(e)), work_bounds)
            if clipped:
                all_busy.append(clipped)

    # Merge busy intervals to get times when at least one person is busy
    merged_busy = merge_intervals(all_busy)

    # Common free time across everyone is the complement within work hours
    common_free = complement_within(work_bounds, merged_busy)

    slot = find_slot(common_free, duration_minutes)
    if not slot:
        raise RuntimeError("No suitable meeting slot found, but problem statement guarantees a solution.")

    start_str, end_str = to_hhmm(slot[0]), to_hhmm(slot[1])

    # Output time range in {HH:MM:HH:MM} format and the day of the week
    print(f"{{{start_str}:{end_str}}}")
    print(day)

if __name__ == "__main__":
    main()