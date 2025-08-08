# Meeting Scheduler for Christine and Helen on Monday

from typing import List, Tuple

TimeRange = Tuple[int, int]  # (start_minute, end_minute)

def to_minutes(hhmm: str) -> int:
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

def subtract_busy_from_window(window: TimeRange, busy: List[TimeRange]) -> List[TimeRange]:
    free = []
    start, end = window
    current = start
    for b_start, b_end in sorted(busy):
        if b_end <= current or b_start >= end:
            continue
        if b_start > current:
            free.append((current, b_start))
        current = max(current, b_end)
        if current >= end:
            break
    if current < end:
        free.append((current, end))
    return free

def intersect_intervals(a: List[TimeRange], b: List[TimeRange]) -> List[TimeRange]:
    i, j = 0, 0
    res = []
    a_sorted = sorted(a)
    b_sorted = sorted(b)
    while i < len(a_sorted) and j < len(b_sorted):
        s = max(a_sorted[i][0], b_sorted[j][0])
        e = min(a_sorted[i][1], b_sorted[j][1])
        if s < e:
            res.append((s, e))
        if a_sorted[i][1] < b_sorted[j][1]:
            i += 1
        else:
            j += 1
    return res

def find_earliest_slot(intervals: List[TimeRange], duration: int, hard_end: int = None) -> TimeRange:
    for s, e in intervals:
        end_cap = min(e, hard_end) if hard_end is not None else e
        if s + duration <= end_cap:
            return (s, s + duration)
    return None

def main():
    # Parameters
    day = "Monday"
    work_start = to_minutes("09:00")
    work_end = to_minutes("17:00")
    duration = 30  # minutes

    # Existing schedules
    christine_busy = [
        (to_minutes("11:00"), to_minutes("11:30")),
        (to_minutes("15:00"), to_minutes("15:30")),
    ]

    helen_busy = [
        (to_minutes("09:30"), to_minutes("10:30")),
        (to_minutes("11:00"), to_minutes("11:30")),
        (to_minutes("12:00"), to_minutes("12:30")),
        (to_minutes("13:30"), to_minutes("16:00")),
        (to_minutes("16:30"), to_minutes("17:00")),
    ]

    # Constraint: Helen cannot meet after 15:00 on Monday
    helen_latest_end = to_minutes("15:00")

    # Compute free windows within work hours
    work_window = (work_start, work_end)
    christine_free = subtract_busy_from_window(work_window, christine_busy)
    helen_free = subtract_busy_from_window(work_window, helen_busy)

    # Intersect availabilities
    common_free = intersect_intervals(christine_free, helen_free)

    # Find earliest slot honoring Helen's latest end
    slot = find_earliest_slot(common_free, duration, hard_end=helen_latest_end)

    if not slot:
        raise SystemExit("No suitable time found, but a solution was expected to exist.")

    start_str = to_hhmm(slot[0])
    end_str = to_hhmm(slot[1])

    # Output format: Day {HH:MM:HH:MM}
    print(f"{day} {{{start_str}:{end_str}}}")

if __name__ == "__main__":
    main()