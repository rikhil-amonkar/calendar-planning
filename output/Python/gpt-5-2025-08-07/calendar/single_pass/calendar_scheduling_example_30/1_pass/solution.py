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

def invert_intervals(busy: List[Tuple[int, int]], window: Tuple[int, int]) -> List[Tuple[int, int]]:
    ws, we = window
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

def intersect_two(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    i, j = 0, 0
    out = []
    while i < len(a) and j < len(b):
        s = max(a[i][0], b[j][0])
        e = min(a[i][1], b[j][1])
        if s < e:
            out.append((s, e))
        if a[i][1] < b[j][1]:
            i += 1
        else:
            j += 1
    return out

def choose_slot(common_free: List[Tuple[int, int]], duration: int, latest_end: int = None) -> Tuple[int, int]:
    # If a latest_end is provided (preference), try to satisfy it first.
    preferred = []
    if latest_end is not None:
        for s, e in common_free:
            end_cap = min(e, latest_end)
            if end_cap - s >= duration:
                preferred.append((s, s + duration))
        if preferred:
            return preferred[0]
    # Fallback: any earliest slot
    for s, e in common_free:
        if e - s >= duration:
            return (s, s + duration)
    return None

def main():
    day = "Monday"
    work_start, work_end = to_minutes("09:00"), to_minutes("17:00")
    work_window = (work_start, work_end)
    duration = 30  # minutes

    # Existing schedules (busy intervals)
    jeffrey_busy = [
        (to_minutes("09:30"), to_minutes("10:00")),
        (to_minutes("10:30"), to_minutes("11:00")),
    ]
    virginia_busy = [
        (to_minutes("09:00"), to_minutes("09:30")),
        (to_minutes("10:00"), to_minutes("10:30")),
        (to_minutes("14:30"), to_minutes("15:00")),
        (to_minutes("16:00"), to_minutes("16:30")),
    ]
    melissa_busy = [
        (to_minutes("09:00"), to_minutes("11:30")),
        (to_minutes("12:00"), to_minutes("12:30")),
        (to_minutes("13:00"), to_minutes("15:00")),
        (to_minutes("16:00"), to_minutes("17:00")),
    ]

    # Preferences
    melissa_latest_end_pref = to_minutes("14:00")  # would rather not meet after 14:00

    # Compute free intervals within work hours
    jeffrey_free = invert_intervals(jeffrey_busy, work_window)
    virginia_free = invert_intervals(virginia_busy, work_window)
    melissa_free = invert_intervals(melissa_busy, work_window)

    # Intersection of all free intervals
    common_free = intersect_two(intersect_two(jeffrey_free, virginia_free), melissa_free)

    # Choose a slot honoring Melissa's preference if possible
    slot = choose_slot(common_free, duration, latest_end=melissa_latest_end_pref)
    if slot is None:
        slot = choose_slot(common_free, duration)

    start_str, end_str = to_hhmm(slot[0]), to_hhmm(slot[1])
    print(f"{{{start_str}:{end_str}}}")
    print(day)

if __name__ == "__main__":
    main()