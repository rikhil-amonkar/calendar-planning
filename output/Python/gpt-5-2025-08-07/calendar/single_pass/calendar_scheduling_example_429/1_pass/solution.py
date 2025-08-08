from typing import List, Tuple

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(minutes: int) -> str:
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
        if s <= last_e:  # overlap or touch
            merged[-1] = (last_s, max(last_e, e))
        else:
            merged.append((s, e))
    return merged

def invert_intervals(intervals: List[Tuple[int, int]], start: int, end: int) -> List[Tuple[int, int]]:
    if not intervals:
        return [(start, end)]
    free = []
    cur = start
    for s, e in intervals:
        if cur < s:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < end:
        free.append((cur, end))
    return free

def find_first_slot(free_intervals: List[Tuple[int, int]], duration: int) -> Tuple[int, int]:
    for s, e in free_intervals:
        if e - s >= duration:
            return (s, s + duration)
    return None

def main():
    day = "Monday"
    work_start = to_minutes("09:00")
    work_end = to_minutes("17:00")
    duration = 30  # minutes

    busy = {
        "Judy":       [("13:00","13:30"), ("16:00","16:30")],
        "Olivia":     [("10:00","10:30"), ("12:00","13:00"), ("14:00","14:30")],
        "Eric":       [],
        "Jacqueline": [("10:00","10:30"), ("15:00","15:30")],
        "Laura":      [("09:00","10:00"), ("10:30","12:00"), ("13:00","13:30"), ("14:30","15:00"), ("15:30","17:00")],
        "Tyler":      [("09:00","10:00"), ("11:00","11:30"), ("12:30","13:00"), ("14:00","14:30"), ("15:30","17:00")],
        "Lisa":       [("09:30","10:30"), ("11:00","11:30"), ("12:00","12:30"), ("13:00","13:30"), ("14:00","14:30"), ("16:00","17:00")],
    }

    # Flatten all busy intervals across participants within work hours
    all_busy: List[Tuple[int, int]] = []
    for intervals in busy.values():
        for s, e in intervals:
            ms, me = max(work_start, to_minutes(s)), min(work_end, to_minutes(e))
            if ms < me:
                all_busy.append((ms, me))

    # Merge to get the union of all busy times
    merged_busy = merge_intervals(all_busy)

    # Invert to get intervals when everyone is free
    everyone_free = invert_intervals(merged_busy, work_start, work_end)

    # Find the first slot that fits the duration
    slot = find_first_slot(everyone_free, duration)
    if not slot:
        raise RuntimeError("No common slot found, but the problem statement guarantees a solution.")

    start_str = to_hhmm(slot[0])
    end_str = to_hhmm(slot[1])

    # Output in the required formats
    print(f"{start_str}:{end_str}")
    print(day)

if __name__ == "__main__":
    main()