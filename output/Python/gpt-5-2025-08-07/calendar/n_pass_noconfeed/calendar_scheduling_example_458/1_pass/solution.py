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

def clamp_intervals(intervals: List[Tuple[int, int]], start: int, end: int) -> List[Tuple[int, int]]:
    clamped = []
    for s, e in intervals:
        s2, e2 = max(s, start), min(e, end)
        if s2 < e2:
            clamped.append((s2, e2))
    return clamped

def invert_within(intervals: List[Tuple[int, int]], start: int, end: int) -> List[Tuple[int, int]]:
    if not intervals:
        return [(start, end)]
    free = []
    cursor = start
    for s, e in intervals:
        if cursor < s:
            free.append((cursor, s))
        cursor = max(cursor, e)
    if cursor < end:
        free.append((cursor, end))
    return free

def find_slot(free: List[Tuple[int, int]], duration: int, preferred_start: int = None) -> Tuple[int, int]:
    # Try to honor preferred_start if provided
    if preferred_start is not None:
        for s, e in free:
            start = max(s, preferred_start)
            if e - start >= duration:
                return (start, start + duration)
    # Fallback: earliest available
    for s, e in free:
        if e - s >= duration:
            return (s, s + duration)
    return None

def main():
    day = "Monday"
    work_start, work_end = to_minutes("09:00"), to_minutes("17:00")
    duration = 30  # minutes

    schedules = {
        "Wayne": [],
        "Melissa": [("10:00", "11:00"), ("12:30", "14:00"), ("15:00", "15:30")],
        "Catherine": [],
        "Gregory": [("12:30", "13:00"), ("15:30", "16:00")],
        "Victoria": [("09:00", "09:30"), ("10:30", "11:30"), ("13:00", "14:00"), ("14:30", "15:00"), ("15:30", "16:30")],
        "Thomas": [("10:00", "12:00"), ("12:30", "13:00"), ("14:30", "16:00")],
        "Jennifer": [("09:00", "09:30"), ("10:00", "10:30"), ("11:00", "13:00"), ("13:30", "14:30"), ("15:00", "15:30"), ("16:00", "16:30")],
    }

    # Collect all busy intervals, clamped to work hours
    all_busy: List[Tuple[int, int]] = []
    for intervals in schedules.values():
        for s, e in intervals:
            all_busy.append((to_minutes(s), to_minutes(e)))
    all_busy = clamp_intervals(all_busy, work_start, work_end)
    all_busy_merged = merge_intervals(all_busy)

    # Common free intervals are work hours minus union of all busy intervals
    common_free = invert_within(all_busy_merged, work_start, work_end)

    # Preference: Wayne would like to avoid meetings before 14:00
    preferred_start = to_minutes("14:00")
    slot = find_slot(common_free, duration, preferred_start=preferred_start)
    if slot is None:
        slot = find_slot(common_free, duration)  # Fallback (should not be needed per problem)

    start_str, end_str = to_hhmm(slot[0]), to_hhmm(slot[1])

    # Output: time range in HH:MM:HH:MM format (in braces as example indicates) and the day
    print(f"{{{start_str}:{end_str}}}")
    print(day)

if __name__ == "__main__":
    main()